// Copyright 2018 PingCAP, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

package core

import (
	"math/bits"

	"github.com/pingcap/tidb/expression"
	"github.com/pingcap/tidb/parser/ast"
)

type joinReorderDPSolver struct {
	*baseSingleGroupJoinOrderSolver
	newJoin func(lChild, rChild LogicalPlan, eqConds []*expression.ScalarFunction, otherConds []expression.Expression) LogicalPlan
}

type joinGroupEqEdge struct {
	nodeIDs []int
	edge    *expression.ScalarFunction
}

type joinGroupNonEqEdge struct {
	nodeIDs    []int
	nodeIDMask uint
	expr       expression.Expression
}

func (s *joinReorderDPSolver) solve(joinGroup []LogicalPlan, eqConds []expression.Expression) (LogicalPlan, error) {
	// TODO: You need to implement the join reorder algo based on DP.

	// The pseudo code can be found in README.
	// And there's some common struct and method like `baseNodeCumCost`, `calcJoinCumCost` you can use in `rule_join_reorder.go`.
	// Also, you can take a look at `rule_join_reorder_greedy.go`, this file implement the join reorder algo based on greedy algorithm.
	// You'll see some common usages in the greedy version.

	// Note that the join tree may be disconnected. i.e. You need to consider the case `select * from t, t1, t2`.
	for _, node := range joinGroup {
		_, err := node.recursiveDeriveStats()
		if err != nil {
			return nil, err
		}
		s.curJoinGroup = append(s.curJoinGroup, &jrNode{
			p:       node,
			cumCost: s.baseNodeCumCost(node),
		})
	}
	adjMatrix := make([][]int, len(s.curJoinGroup))
	totalEqEdges := make([]joinGroupEqEdge, 0, len(eqConds))
	// build join tree
	for _, cond := range eqConds {
		f := cond.(*expression.ScalarFunction)
		lCol := f.GetArgs()[0].(*expression.Column)
		rCol := f.GetArgs()[1].(*expression.Column)
		lIndex, err := findNodeIndexInGroup(joinGroup, lCol)
		if err != nil {
			return nil, err
		}
		rIndex, err := findNodeIndexInGroup(joinGroup, rCol)
		if err != nil {
			return nil, err
		}
		totalEqEdges = append(totalEqEdges, joinGroupEqEdge{
			nodeIDs: []int{lIndex, rIndex},
			edge:    f,
		})
		adjMatrix[lIndex] = append(adjMatrix[lIndex], rIndex)
		adjMatrix[rIndex] = append(adjMatrix[rIndex], lIndex)
	}
	totalNonEqEdges := make([]joinGroupNonEqEdge, 0, len(s.otherConds))
	for _, cond := range s.otherConds {
		cols := expression.ExtractColumns(cond)
		mask := uint(0)
		ids := make([]int, 0, len(cols))
		for _, col := range cols {
			idx, err := findNodeIndexInGroup(joinGroup, col)
			if err != nil {
				return nil, err
			}
			ids = append(ids, idx)
			mask |= 1 << uint(idx)
		}
		totalNonEqEdges = append(totalNonEqEdges, joinGroupNonEqEdge{
			nodeIDs:    ids,
			nodeIDMask: mask,
			expr:       cond,
		})
	}
	// bfs join graph
	visited := make([]bool, len(joinGroup))
	nodeID2VisitID := make([]int, len(joinGroup))
	var joins []LogicalPlan
	for i := 0; i < len(joinGroup); i++ {
		if visited[i] {
			continue
		}
		visitID2NodeID := s.bfsJoinGraph(i, visited, adjMatrix, nodeID2VisitID)
		nodeIDMask := uint(0)
		for _, id := range visitID2NodeID {
			nodeIDMask |= 1 << uint(id)
		}
		var subNonEqEdges []joinGroupNonEqEdge
		for i := len(totalNonEqEdges) - 1; i >= 0; i-- {
			if totalNonEqEdges[i].nodeIDMask&nodeIDMask != totalNonEqEdges[i].nodeIDMask {
				// 当前 edge 不存在于 nodeIDMask 对应的 sub 中
				continue
			}
			newMask := uint(0)
			for _, nodeID := range totalNonEqEdges[i].nodeIDs {
				newMask |= 1 << uint(nodeID2VisitID[nodeID])
			}
			totalNonEqEdges[i].nodeIDMask = newMask
			subNonEqEdges = append(subNonEqEdges, totalNonEqEdges[i])
			// remove non eq edge i
			totalNonEqEdges = append(totalNonEqEdges[:i], totalNonEqEdges[i+1:]...)
		}
		// do dp
		join, err := s.doDP(visitID2NodeID, nodeID2VisitID, joinGroup, totalEqEdges, subNonEqEdges)
		if err != nil {
			return nil, err
		}
		joins = append(joins, join)
	}
	remainedOtherCond := make([]expression.Expression, 0, len(totalNonEqEdges))
	for _, edge := range totalNonEqEdges {
		remainedOtherCond = append(remainedOtherCond, edge.expr)
	}
	return s.makeBushyJoin(joins, remainedOtherCond), nil
}

func (s *joinReorderDPSolver) doDP(
	visitID2NodeID,
	nodeID2VisitID []int,
	joinGroup []LogicalPlan,
	totalEqEdges []joinGroupEqEdge,
	totalNonEqEdges []joinGroupNonEqEdge) (LogicalPlan, error) {
	nodeCnt := uint(len(visitID2NodeID))
	dp := make([]*jrNode, 1<<nodeCnt)
	for i := uint(0); i < nodeCnt; i++ {
		dp[1<<i] = s.curJoinGroup[visitID2NodeID[i]]
	}
	for nodeBitMap := uint(1); nodeBitMap < (1 << nodeCnt); nodeBitMap++ {
		if bits.OnesCount(nodeBitMap) == 1 {
			continue
		}
		// f[group] = min{join{f[sub], f[group ^ sub])}
		for sub := (nodeBitMap - 1) & nodeBitMap; sub > 0; sub = (sub - 1) & nodeBitMap {
			remain := nodeBitMap ^ sub
			if sub > remain {
				continue
			}
			// not connected
			if dp[sub] == nil || dp[remain] == nil {
				continue
			}
			edges, otherConds := s.getConnectedNodes(sub, remain, nodeID2VisitID, totalEqEdges, totalNonEqEdges)
			if len(edges) == 0 {
				continue
			}
			join, err := s.newJoinWithEdge(dp[sub].p, dp[remain].p, edges, otherConds)
			if err != nil {
				return nil, err
			}
			cost := s.calcJoinCumCost(join, dp[sub], dp[remain])
			if dp[nodeBitMap] == nil {
				dp[nodeBitMap] = &jrNode{
					p:       join,
					cumCost: cost,
				}
			} else if dp[nodeBitMap].cumCost > cost {
				dp[nodeBitMap].p = join
				dp[nodeBitMap].cumCost = cost
			}
		}
	}
	return dp[(1<<nodeCnt)-1].p, nil
}

func (s *joinReorderDPSolver) getConnectedNodes(
	leftMask, rightMask uint,
	nodeID2VisitID []int,
	totalEqEdges []joinGroupEqEdge,
	totalNonEqEdges []joinGroupNonEqEdge) ([]joinGroupEqEdge, []expression.Expression) {
	var edges []joinGroupEqEdge
	var otherConds []expression.Expression
	for _, edge := range totalEqEdges {
		lIndex := uint(nodeID2VisitID[edge.nodeIDs[0]])
		rIndex := uint(nodeID2VisitID[edge.nodeIDs[1]])
		if ((leftMask&(1<<lIndex)) > 0 && (rightMask&(1<<rIndex)) > 0) ||
			((leftMask&(1<<rIndex)) > 0 && (rightMask&(1<<lIndex)) > 0) {
			edges = append(edges, edge)
		}
	}
	for _, edge := range totalNonEqEdges {
		if edge.nodeIDMask&(leftMask|rightMask) != edge.nodeIDMask {
			continue
		}
		if edge.nodeIDMask&leftMask == 0 || edge.nodeIDMask&rightMask == 0 {
			continue
		}
		otherConds = append(otherConds, edge.expr)
	}
	return edges, otherConds
}

func (s *joinReorderDPSolver) bfsJoinGraph(start int, visited []bool, matrix [][]int, nodeID2VisitID []int) []int {
	q := []int{start}
	visited[start] = true
	var visitID2NodeID []int
	for len(q) > 0 {
		// q.front()
		cur := q[0]
		// q.pop()
		q = q[1:]
		// map of node id and visit id
		// 建立 node id 与 访问顺序 的映射
		nodeID2VisitID[cur] = len(visitID2NodeID)
		visitID2NodeID = append(visitID2NodeID, cur)
		for _, next := range matrix[cur] {
			if !visited[next] {
				q = append(q, next)
				visited[next] = true
			}
		}
	}
	return visitID2NodeID
}

func (s *joinReorderDPSolver) newJoinWithEdge(leftPlan, rightPlan LogicalPlan, edges []joinGroupEqEdge, otherConds []expression.Expression) (LogicalPlan, error) {
	var eqConds []*expression.ScalarFunction
	for _, edge := range edges {
		lCol := edge.edge.GetArgs()[0].(*expression.Column)
		rCol := edge.edge.GetArgs()[1].(*expression.Column)
		if leftPlan.Schema().Contains(lCol) {
			eqConds = append(eqConds, edge.edge)
		} else {
			newSf := expression.NewFunctionInternal(s.ctx, ast.EQ, edge.edge.GetType(), rCol, lCol).(*expression.ScalarFunction)
			eqConds = append(eqConds, newSf)
		}
	}
	join := s.newJoin(leftPlan, rightPlan, eqConds, otherConds)
	_, err := join.recursiveDeriveStats()
	return join, err
}

// Make cartesian join as bushy tree.
func (s *joinReorderDPSolver) makeBushyJoin(cartesianJoinGroup []LogicalPlan, otherConds []expression.Expression) LogicalPlan {
	for len(cartesianJoinGroup) > 1 {
		resultJoinGroup := make([]LogicalPlan, 0, len(cartesianJoinGroup))
		for i := 0; i < len(cartesianJoinGroup); i += 2 {
			if i+1 == len(cartesianJoinGroup) {
				resultJoinGroup = append(resultJoinGroup, cartesianJoinGroup[i])
				break
			}
			// TODO:Since the other condition may involve more than two tables, e.g. t1.a = t2.b+t3.c.
			//  So We'll need a extra stage to deal with it.
			// Currently, we just add it when building cartesianJoinGroup.
			mergedSchema := expression.MergeSchema(cartesianJoinGroup[i].Schema(), cartesianJoinGroup[i+1].Schema())
			var usedOtherConds []expression.Expression
			otherConds, usedOtherConds = expression.FilterOutInPlace(otherConds, func(expr expression.Expression) bool {
				return expression.ExprFromSchema(expr, mergedSchema)
			})
			resultJoinGroup = append(resultJoinGroup, s.newJoin(cartesianJoinGroup[i], cartesianJoinGroup[i+1], nil, usedOtherConds))
		}
		cartesianJoinGroup = resultJoinGroup
	}
	return cartesianJoinGroup[0]
}

func findNodeIndexInGroup(group []LogicalPlan, col *expression.Column) (int, error) {
	for i, plan := range group {
		if plan.Schema().Contains(col) {
			return i, nil
		}
	}
	return -1, ErrUnknownColumn.GenWithStackByArgs(col, "JOIN REORDER RULE")
}
