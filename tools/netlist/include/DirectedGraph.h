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
#include <cassert>

/// A class to represent a directed edge in the graph.
template<class NodeType, class EdgeType>
class DirectedEdge {
public:
  DirectedEdge(NodeType &targetNode) : targetNode(targetNode) {}
protected:
  NodeType &targetNode;
};

/// A class to represent a node in the graph.
template<class NodeType, class EdgeType>
class Node {
public:
  using EdgeListType = std::vector<std::unique_ptr<EdgeType>>;
  using iterator = typename EdgeListType::iterator;
  using const_iterator = typename EdgeListType::const_iterator;

  Node() = default;
  Node(EdgeType &edge) : edges() { edges.push_back(edge); }

  const_iterator begin() const { return edges.begin(); }
  const_iterator end() const { return edges.end(); }
  iterator begin() { return edges.begin(); }
  iterator end() { return edges.end(); }

  /// Add an edge between this node and a target node.
  EdgeType *addEdge(NodeType &targetNode) {
    auto edge = std::make_unique<EdgeType>(targetNode);
    edges.emplace_back(std::move(edge));
    return edges.back().get();
  }

  //EdgeType getEdge()

  //void removeEdge(EdgeType &edge) { edges.remove(&edge); }

  void clearEdges() { edges.clear(); }

private:
  EdgeListType edges;
};

template<class NodeType, class EdgeType>
class DirectedGraph {
private:
  using NodeListType = std::vector<std::unique_ptr<NodeType>>;
  using EdgeListType = std::vector<std::unique_ptr<EdgeType>>;
public:
  using iterator = typename NodeListType::iterator;
  using const_iterator = typename NodeListType::const_iterator;
  using node_descriptor = size_t;
  using edge_descriptor = EdgeType*;
  using DirectedGraphType = DirectedGraph<NodeType, EdgeType>;

  DirectedGraph() = default;

  // Find a given node.
  //const_iterator findNode(const NodeType &nodeToFind) const {
  //  return std::find_if(nodes,
  //                      [&nodeToFind](const NodeType *node) { return *node == nodeToFind; });
  //}

  /// Add a node to the graph and return a descriptor.
  node_descriptor addNode() {
    nodes.push_back(std::make_unique<NodeType>());
    return nodes.size() - 1;
  }

  /// Add an edge between two existing nodes in the graph.
  edge_descriptor addEdge(node_descriptor sourceNode, node_descriptor targetNode) {
    assert(sourceNode < nodes.size() && "Source node does not exist");
    assert(targetNode < nodes.size() && "Target node does not exist");
    return nodes[sourceNode]->addEdge(*nodes[targetNode]);
  }

  /// Retrieve a node by its descriptor.
  NodeType &getNode(node_descriptor node) {
    assert(node < nodes.size() && "Node does not exist");
    return nodes[node];
  }

  /// Return the size of the graph.
  size_t size() { return nodes.size(); }

private:
  NodeListType nodes;
};

