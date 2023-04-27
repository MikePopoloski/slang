//------------------------------------------------------------------------------
//! @file DirectedGraph.h
//! @brief Directed graph ADT
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <algorithm>
#include <cassert>
#include <limits>
#include <memory>
#include <vector>

namespace netlist {

// Inspired by LLVM's DirectedGraph ADT.
// https://llvm.org/doxygen/DirectedGraph_8h_source.html

/// A class to represent a directed edge in a graph.
template<class NodeType, class EdgeType>
class DirectedEdge {
public:
  DirectedEdge(NodeType &sourceNode, NodeType &targetNode)
    : sourceNode(sourceNode), targetNode(targetNode) {}

  DirectedEdge<NodeType, EdgeType> &operator=(const DirectedEdge<NodeType, EdgeType> &edge) {
    sourceNode = edge.sourceNode;
    targetNode = edge.targetNode;
    return *this;
  }

  bool operator==(const EdgeType &E) const { return getDerived().isEqualTo(E); }
  bool operator!=(const EdgeType &E) const { return !operator==(E); }

  /// Return the source node of this edge.
  NodeType &getSourceNode() const { return sourceNode; }

  /// Return the target node of this edge.
  NodeType &getTargetNode() const { return targetNode; }

protected:
  // As the default implementation use address comparison for equality.
  bool isEqualTo(const EdgeType &edge) const { return this == &edge; }

  // Cast the 'this' pointer to the derived type and return a reference.
  EdgeType &getDerived() {
    return *static_cast<EdgeType*>(this);
  }
  const EdgeType &getDerived() const {
    return *static_cast<const EdgeType*>(this);
  }

  NodeType &sourceNode;
  NodeType &targetNode;
};

/// A class to represent a node in a directed graph.
template<class NodeType, class EdgeType>
class Node {
public:
  using EdgeListType = std::vector<std::unique_ptr<EdgeType>>;
  using iterator = typename EdgeListType::iterator;
  using const_iterator = typename EdgeListType::const_iterator;
  using edge_descriptor = EdgeType*;

  Node() = default;
  Node(EdgeType &edge) : edges() { edges.push_back(edge); }
  virtual ~Node() = default;

  const_iterator begin() const { return edges.begin(); }
  const_iterator end() const { return edges.end(); }
  iterator begin() { return edges.begin(); }
  iterator end() { return edges.end(); }

  Node<NodeType, EdgeType> &operator=(const Node<NodeType, EdgeType> &node) {
    edges = node.edges;
    return *this;
  }
  Node<NodeType, EdgeType> &operator=(Node<NodeType, EdgeType> &&node) noexcept {
    edges = std::move(node.Edges);
    return *this;
  }

  /// Static polymorphism: delegate implementation (via isEqualTo) to the
  /// derived class. Add friend operator to resolve ambiguity between operand
  /// ordering with C++20.
  friend bool operator==(NodeType const &A, NodeType const& B) noexcept {
    return A.getDerived().isEqualTo(B);
  }
  bool operator==(const NodeType &N) const { return getDerived().isEqualTo(N); }
  bool operator!=(const NodeType &N) const { return !operator==(N); }

  /// Return an iterator to the edge connecting the target node.
  const_iterator findEdgeTo(NodeType &targetNode) {
    return std::find_if(edges.begin(), edges.end(),
                        [&targetNode](std::unique_ptr<EdgeType> &edge) {
                          return edge->getTargetNode() == targetNode;
                        });
  }

  /// Add an edge between this node and a target node, only if it does not
  /// already exist. Return a pointer to the newly-created edge.
  EdgeType &addEdge(NodeType &targetNode) {
    auto edgeIt = findEdgeTo(targetNode);
    if (edgeIt == edges.end()) {
      auto edge = std::make_unique<EdgeType>(getDerived(), targetNode);
      edges.emplace_back(std::move(edge));
      return *(edges.back().get());
    } else {
      return *((*edgeIt).get());
    }
  }

  /// Remove an edge between this node and a target node.
  /// Return true if the edge existed and was removed, and false otherwise.
  bool removeEdge(NodeType &targetNode) {
    auto edgeIt = findEdgeTo(targetNode);
    if (edgeIt != edges.end()) {
      edges.erase(edgeIt);
      return true;
    } else {
      return false;
    }
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

  /// Return the list of outgoing edges from this node.
  const EdgeListType &getEdges() const { return edges; }

  /// Return the total number of edges outgoing from this node.
  size_t outDegree() const { return edges.size(); }

  /// Remove all edges outgoing from this node.
  void clearEdges() { edges.clear(); }

protected:
  // As the default implementation use address comparison for equality.
  bool isEqualTo(const NodeType &node) const {
    return this == &node;
  }
  // Cast the 'this' pointer to the derived type and return a reference.
  NodeType &getDerived() {
    return *static_cast<NodeType*>(this);
  }
  const NodeType &getDerived() const {
    return *static_cast<const NodeType*>(this);
  }

  EdgeListType edges;
};

/// A directed graph.
/// Nodes and edges are stored in an adjacency list data structure, where the
/// DirectedGraph contains a vector of nodes, and each node contains a vector
/// of directed edges to other nodes. Multi-edges are not permitted.
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
  const size_t null_node = std::numeric_limits<size_t>::max();

  DirectedGraph() = default;

  const_iterator begin() const { return nodes.begin(); }
  const_iterator end() const { return nodes.end(); }
  iterator begin() { return nodes.begin(); }
  iterator end() { return nodes.end(); }

  node_descriptor findNode(const NodeType &nodeToFind) const {
    auto it = std::find_if(nodes.begin(), nodes.end(),
                           [&nodeToFind](const std::unique_ptr<NodeType> &node) {
                             return const_cast<const NodeType&>(*node) == nodeToFind;
                           });
    if (it == nodes.end()) {
      return null_node;
    } else {
      return it - nodes.begin();
    }
  }

  /// Add a node to the graph and return a reference to it.
  NodeType &addNode() {
    nodes.push_back(std::make_unique<NodeType>());
    return *(nodes.back().get());
  }

  /// Add an existing node to the graph and return a reference to it.
  NodeType &addNode(std::unique_ptr<NodeType> node) {
    nodes.push_back(std::move(node));
    return *(nodes.back().get());
  }

  /// Remove the specified node from the graph, including all edges that are
  /// incident upon this node, and all edges that are outgoing from this node.
  /// Return true if the node exists and was removed and false if it didn't
  /// exist.
  bool removeNode(node_descriptor nodeToRemove) {
    if (nodeToRemove >= nodes.size()) {
      // The node is not in the graph.
      return false;
    }
    // Remove incoming edges to node for removal.
    std::vector<EdgeType*> edgesToRemove;
    for (auto &node : nodes) {
      if (getNode(nodeToRemove) == *node) {
        // Skip the node to remove.
        continue;
      }
      node->getEdgesTo(getNode(nodeToRemove), edgesToRemove);
      for (auto *edge : edgesToRemove) {
        node->removeEdge(getNode(nodeToRemove));
      }
      edgesToRemove.clear();
    }
    // Remove the outgoing edges from the node for removal.
    nodes[nodeToRemove]->clearEdges();
    // Remove the node itself.
    nodes.erase(std::next(nodes.begin(), nodeToRemove));
    return true;
  }

  /// Add an edge between two existing nodes in the graph.
  EdgeType &addEdge(node_descriptor sourceNode, node_descriptor targetNode) {
    assert(sourceNode < nodes.size() && "Source node does not exist");
    assert(targetNode < nodes.size() && "Target node does not exist");
    return nodes[sourceNode]->addEdge(getNode(targetNode));
  }

  /// Remove an edge between the two specified vertices. Return true if the
  /// edge exists and was removed, and false if it didn't exist.
  bool removeEdge(node_descriptor sourceNode, node_descriptor targetNode) {
    assert(sourceNode < nodes.size() && "Source node does not exist");
    assert(targetNode < nodes.size() && "Target node does not exist");
    return nodes[sourceNode]->removeEdge(getNode(targetNode));
  }

  /// Retrieve a node by its descriptor.
  NodeType &getNode(node_descriptor node) {
    assert(node < nodes.size() && "Node does not exist");
    return *nodes[node];
  }

  /// Return the descriptor for a particular node.
  node_descriptor getNodeDescriptor(NodeType &node) {
    return &node - nodes.data();
  }

  /// Collect all edges that are incident to the specified node.
  /// Return true if at least one edge was found and false otherwise.
  bool getInEdgesToNode(node_descriptor nodeDesc, std::vector<EdgeType*> &results) const {
    assert(results.empty() && "Expected the results parameter to be empty");
    std::vector<EdgeType*> tempResults;
    for (auto &node : nodes) {
      node->getEdgesTo(getNode(nodeDesc), tempResults);
      results.insert(results.end(), tempResults.begin(), tempResults.end());
      tempResults.clear();
    }
    return !results.empty();
  }

  /// Return the number of edges eminating from the specified node.
  size_t outDegree(node_descriptor nodeDesc) const {
    assert(nodeDesc < nodes.size() && "Node does not exist");
    return nodes[nodeDesc]->outDegree();
  }

  /// Return the number of edges incident to the specified node.
  size_t inDegree(node_descriptor nodeDesc) const {
    assert(nodeDesc < nodes.size() && "Node does not exist");
    std::vector<EdgeType*> results;
    getInEdgesToNode(nodeDesc, results);
    return results.size();
  }

  bool removeNode(NodeType &node) {
    return removeNode(findNode(node));
  }

  EdgeType &addEdge(const NodeType &sourceNode, const NodeType &targetNode) {
    return addEdge(findNode(sourceNode), findNode(targetNode));
  }

  bool removeEdge(NodeType &sourceNode, NodeType &targetNode) {
    return removeEdge(findNode(sourceNode), findNode(targetNode));
  }

  const NodeType &getNode(node_descriptor node) const {
    assert(node < nodes.size() && "Node does not exist");
    return *nodes[node];
  }

  size_t outDegree(const NodeType &node) const {
    return outDegree(findNode(node));
  }

  size_t inDegree(const NodeType &node) const {
    return inDegree(findNode(node));
  }

  /// Return the size of the graph.
  size_t numNodes() const { return nodes.size(); }

  /// Return the number of edges in the graph.
  size_t numEdges() const {
    size_t count = 0;
    for (auto &node : nodes) {
      count += node->outDegree();
    }
    return count;
  }

protected:
  NodeListType nodes;
};

} // End namespace netlist.
