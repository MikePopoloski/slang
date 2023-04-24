//------------------------------------------------------------------------------
//! @file DepthFirstIterator.h
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
class DepthFirstIterator {
public:
  using GraphType = DirectedGraph<NodeType, EdgeType>;
  using iterator_category = std::forward_iterator_tag;
  using difference_type = std::ptrdiff_t;
  using value_type = NodeType;
  using pointer = NodeType*;
  using reference = NodeType&;

  DepthFirstIterator(const NodeType &startNode) {
    visitedNodes.insert(startNode);
    visitStack.push_back(StackElement(startNode, startNode.begin()));
  }

  DepthFirstIterator() = default;

private:
  using EdgeIteratorType = typename GraphType::iterator;
  using VisitStackElement = std::pair<NodeType&, EdgeIteratorType>;

  /// Perform a depth-first search, terminating when targetNode is reached.
  void next() {
    do {
      // Take the top node on the visit stack.
      auto &node = visitStack.back().first;
      auto &nodeIt = visitStack.back().second;
      // Visit each child node that hasn't already been visited.
      while (nodeIt != node.end()) {
        const auto targetNode = nodeIt.second.getTargetNode();
        if (visitedNodes.count(targetNode) == 0) {
          // Push a new 'current' node onto the stack.
          visitStack.push_back(VisitStackElement(targetNode, targetNode.begin()));
          return;
        }
        nodeIt++;
      }
      // Visited all children of this node.
      visitStack.pop_back();
    } while (!visitStack.empty());
  }

public:
  static DepthFirstIterator begin(const NodeType &startNode) {
    return DepthFirstIterator(startNode);
  }
  static DepthFirstIterator end() {
    return DepthFirstIterator();
  }

  reference operator*() const { return visitStack.back(); }

  pointer operator->() { return &visitStack.back(); }

  /// Prefix increment
  DepthFirstIterator& operator++() {
    next();
    return *this;
  }

  /// Postfix increment
  DepthFirstIterator operator++(int) {
    DepthFirstIterator tmp = *this;
    ++(*this);
    return tmp;
  }

  friend bool operator== (const DepthFirstIterator& a, const DepthFirstIterator& b) {
    return a.visitStack == b.visitStack;
  };

  friend bool operator!= (const DepthFirstIterator& a, const DepthFirstIterator& b) {
    return a.visitStack != b.visitStack;;
  };

private:
  std::set<NodeType&> visitedNodes;
  std::vector<NodeType&> visitStack;
};
