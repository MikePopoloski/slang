//------------------------------------------------------------------------------
//! @file DepthFirstSearch.h
//! @brief Implementation of depth-first search of a directed graph.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <set>
#include <vector>

#include "DirectedGraph.h"

namespace netlist {

/// A visitor class to be implemented that provides an interface to the
/// depth-first traversal pattern.
template<class NodeType, class EdgeType>
struct DepthFirstSearchVisitor {
  virtual void visitNode(NodeType &node) = 0;
  virtual void visitEdge(EdgeType &edge) = 0;
};

template<class NodeType, class EdgeType>
class DepthFirstSearch {
public:
  DepthFirstSearch(DepthFirstSearchVisitor<NodeType, EdgeType> &visitor, NodeType &startNode)
    : visitor(visitor) {
    visitedNodes.insert(&startNode);
    visitStack.push_back(VisitStackElement(startNode, startNode.begin()));
    visitor.visitNode(startNode);
    run();
  }

private:
  using EdgeIteratorType = typename NodeType::iterator;
  using VisitStackElement = std::pair<NodeType&, EdgeIteratorType>;

  /// Perform a depth-first traversal, calling the visitor methods on the way.
  void run() {
    while (!visitStack.empty()) {
      auto &node = visitStack.back().first;
      auto &nodeIt = visitStack.back().second;
      // Visit each child node that hasn't already been visited.
      while (nodeIt != node.end()) {
        auto *edge = nodeIt->get();
        auto &targetNode = edge->getTargetNode();
        nodeIt++;
        if (visitedNodes.count(&targetNode) == 0) {
          // Push a new 'current' node onto the stack and mark it as visited.
          visitStack.push_back(VisitStackElement(targetNode, targetNode.begin()));
          visitedNodes.insert(&targetNode);
          visitor.visitEdge(*edge);
          visitor.visitNode(targetNode);
          return run();
        }
      }
      // All children of this node have been visited or skipped, so remove from the stack.
      visitStack.pop_back();
    }
  }

private:
  DepthFirstSearchVisitor<NodeType, EdgeType> &visitor;
  std::set<const NodeType*> visitedNodes;
  std::vector<VisitStackElement> visitStack;
};

} // End namespace netlist.
