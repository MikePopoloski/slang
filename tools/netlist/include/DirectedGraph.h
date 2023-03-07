//------------------------------------------------------------------------------
//! @file DirectedGraph.h 
//! @brief Directed graph ADT
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <algorithm>
#include <memory>
#include <vector>

// Directed graph ADT based on LLVM's
// https://llvm.org/doxygen/DirectedGraph_8h_source.html

template <class GraphType>
struct GraphTraits {
  using NodeDescriptor = typename GraphType::UnknownGraphTypeError;
  using EdgeDescriptor = typename GraphType::UnknownGraphTypeError;
  static inline NodeDescriptor nullNode() {
    return GraphType::nullNode();
  }
};

//template <> struct GraphTraits<DirectedGraph*> {
//  using NodeDescriptor = size_t;
//  using EdgeDescriptor = size_t;
//}

template<class NodeType, class EdgeType>
class DirectedEdge {
public:
  DirectedEdge() = delete;
  explicit DirectedEdge(NodeType &targetNode) : targetNode(targetNode) {}
private:
  NodeType &targetNode;
};

template<class NodeType, class EdgeType>
class Node {
public:
  using EdgeListType = std::vector<EdgeType*>;
  using iterator = typename EdgeListType::iterator;
  using const_iterator = typename EdgeListType::const_iterator;

  Node() = default;
  Node(EdgeType &edge) : edges() { edges.push_back(edge); }

  const_iterator begin() const { return edges.begin(); }
  const_iterator end() const { return edges.end(); }
  iterator begin() { return edges.begin(); }
  iterator end() { return edges.end(); }

  bool addEdge(EdgeType &edge) { return edges.insert(&edge); }
  void removeEdge(EdgeType &edge) { edges.remove(&edge); }
  void clearEdges() { edges.clear(); }

private:
  std::vector<EdgeType*> edges;
};

template<class NodeType, class EdgeType>
class DirectedGraph {
private:
  using NodeListType = std::vector<std::unique_ptr<NodeType>>;
  using EdgeListType = std::vector<std::unique_ptr<EdgeType>>;
public:
  using iterator = typename NodeListType::iterator;
  using const_iterator = typename NodeListType::const_iterator;
  using DirectedGraphType = DirectedGraph<NodeType, EdgeType>;
  using node_descriptor = typename GraphTraits<DirectedGraph>::node_descriptor;
  using edge_descriptor = typename GraphTraits<DirectedGraph>::edge_descriptor;

  DirectedGraph() = default;

  // Find a given node.
  const_iterator findNode(const NodeType &nodeToFind) const {
    return std::find_if(nodes, 
                        [&nodeToFind](const NodeType *node) { return *node == nodeToFind; });
  }

  /// Add a node to the graph and return a descriptor.
  NodeDescriptor addNode() {
    nodes.push_back(std::make_unique<NodeType>());
    return nodes.size() - 1;
  }

  /// Add an edge between two existing nodes in the graph.
  void addEdge(NodeDescriptor sourceNode, NodeDescriptor targetNode) {
    auto sourceIt = findNode(sourceNode);
    auto targetIt = findNode(targetNode);
    assert(sourceIt != nodes.end() && "Source node does not exist");
    assert(targetIt != nodes.end() && "Target node does not exist");
    (*sourceIt)->addEdge();
  }
  
  size_t size() { return nodes.size(); }

private:
  NodeListType nodes;
};

