//------------------------------------------------------------------------------
//! @file DepthFirstIterator.h
//! @brief Implementation of depth-first traversal of a directed graph with an
//         iterator that provides access to edges.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <set>
#include <vector>

#include <iostream> //DEBUG

#include "DirectedGraph.h"

namespace netlist {

template<class NodeType, class EdgeType>
class DepthFirstIterator {
public:
  using iterator_category = std::forward_iterator_tag;
  using difference_type = std::ptrdiff_t;
  using value_type = EdgeType;
  using pointer = EdgeType*;
  using reference = EdgeType&;

  DepthFirstIterator() = default;

  DepthFirstIterator(NodeType &startNode) {
    visitedNodes.insert(&startNode);
    visitStack.push_back(VisitStackElement(startNode, startNode.begin()));
  }

private:
  using EdgeIteratorType = typename NodeType::iterator;
  using VisitStackElement = std::pair<NodeType&, EdgeIteratorType>;

  /// Perform an iteration of depth-first traversal.
  void next() {
    do {
      // Take the top node on the visit stack.
      auto &node = visitStack.back().first;
      auto &nodeIt = visitStack.back().second;
      // Visit each child node that hasn't already been visited.
      while (nodeIt != node.end()) {
        auto &targetNode = (*nodeIt)->getTargetNode();
        if (visitedNodes.count(&targetNode) == 0) {
          // Push a new 'current' node onto the stack.
          visitStack.push_back(VisitStackElement(targetNode, targetNode.begin()));
          visitedNodes.insert(&targetNode);
          return;
        }
        nodeIt++;
      }
      // Visited all children of this node.
      visitStack.pop_back();
    } while (!visitStack.empty());
  }

public:
  static DepthFirstIterator begin(NodeType &startNode) {
    return DepthFirstIterator(startNode);
  }
  static DepthFirstIterator end() {
    return DepthFirstIterator();
  }

  reference operator*() const {
    auto it = visitStack.back().second;
    return *(it->get());
  }

  pointer operator->() {
    auto it = visitStack.back().second;
    return it->get();
  }

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
  std::set<const NodeType*> visitedNodes;
  std::vector<VisitStackElement> visitStack;
};

} // End namespace netlist.
