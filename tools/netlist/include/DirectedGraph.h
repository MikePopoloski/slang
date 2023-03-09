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

// Inspired by LLVM's DirectedGraph ADT.
// https://llvm.org/doxygen/DirectedGraph_8h_source.html

/// A class to represent a directed edge in the graph.
template<class NodeType, class EdgeType>
class DirectedEdge {
public:
  DirectedEdge(NodeType &targetNode) : targetNode(targetNode) {}

  DirectedEdge<NodeType, EdgeType> &operator=(const DirectedEdge<NodeType, EdgeType> &edge) {
    targetNode = edge.targetNode;
    return *this;
  }

  const NodeType &getTargetNode() { return targetNode; }

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
  using edge_descriptor = EdgeType*;

  Node() = default;
  Node(EdgeType &edge) : edges() { edges.push_back(edge); }

  const_iterator begin() const { return edges.begin(); }
  const_iterator end() const { return edges.end(); }
  iterator begin() { return edges.begin(); }
  iterator end() { return edges.end(); }

  Node<NodeType, EdgeType> &operator=(const Node<NodeType, EdgeType> &node) {
    edges = node.edges;
    return *this;
  }
  Node<NodeType, EdgeType> &operator=(const Node<NodeType, EdgeType> &&node) {
    edges = std::move(node.Edges);
    return *this;
  }

  /// Static polymorphism: delegate implementation (via isEqualTo) to the
  /// derived class.
  bool operator==(const NodeType &N) const { return getDerived().isEqualTo(N); }
  bool operator!=(const NodeType &N) const { return !operator==(N); }

  /// Add an edge between this node and a target node.
  EdgeType *addEdge(NodeType &targetNode) {
    auto edge = std::make_unique<EdgeType>(targetNode);
    edges.emplace_back(std::move(edge));
    return edges.back().get();
  }

  /// Populate a result vector of edges from this node to the specified target
  /// node. Return true if at least one edge was found.
  bool getEdgesTo(const NodeType &targetNode, std::vector<EdgeType*> &result) {
    assert(result.empty() && "Expected the results parameter to be empty");
    for (auto &edge : edges) {
      if (edge->getTargetNode() == targetNode) {
        result.push_back(edge.get());
      }
    }
    return !result.empty();
  }

  void removeEdge(EdgeType &edge) { edges.remove(&edge); }

  const EdgeListType &getEdges() const { return edges; }

  size_t outDegree() const { return edges.size(); }

  void clearEdges() { edges.clear(); }

protected:
  // As the default implementation use address comparison for equality.
  bool isEqualTo(const NodeType &N) const {
    return this == &N;
  }
  NodeType &getDerived() {
    return *static_cast<NodeType*>(this);
  }
  const NodeType &getDerived() const {
    return *static_cast<const NodeType*>(this);
  }

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
    return *nodes[node];
  }

  /// Collect all edges that
  bool getInEdgesToNode(node_descriptor nodeDesc, std::vector<EdgeType*> &results) const {
    assert(results.empty() && "Expected the results parameter to be empty");
    std::vector<EdgeType*> tempResults;
    for (auto &node : nodes) {
      node->getEdgesTo(*(nodes[nodeDesc].get()), tempResults);
      results.insert(results.end(), tempResults.begin(), tempResults.end());
      tempResults.clear();
    }
    return !results.empty();
  }

  /// Return the number of edges incident on the specified node.
  size_t inDegree(node_descriptor nodeDesc) {
    std::vector<EdgeType*> results;
    getInEdgesToNode(nodeDesc, results);
    return results.size();
  }

  /// Return the size of the graph.
  size_t size() { return nodes.size(); }

private:
  NodeListType nodes;
};

