//------------------------------------------------------------------------------
//! @file DepthFirstSearch.h
//! @brief Implementation of depth-first search for a directed graph.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <set>
#include <vector>

#include "DirectedGraph.h"

template<class NodeType, class EdgeType>
class DepthFirstSearch {
public:
  DepthFirstSearch(DirectedGraph<NodeType, EdgeType> &graph) : graph(graph) {}

  /// Perform a depth-first search, terminating when targetNode is reached.
  void search(NodeType &sourceNode, NodeType &targetNode) {
    //visitedNodes.insert(sourceNode);
    //visitStack.push_back(sourceNode);
    //for (const auto it = sourceNode.begin(); it != sourceNode.end(); it++) {
    //  const auto targetNode = it.second.getTargetNode();
    //  if (visitedNodes.count(targetNode) == 0) {
    //    visitStack.push_back(targetNode);
    //  }
    //}
  }

private:
  DirectedGraph<NodeType, EdgeType> &graph;
  std::set<NodeType&> visitedNodes;
  std::vector<NodeType&> visitStack;
};
