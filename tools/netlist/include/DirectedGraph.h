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

#include "slang/util/Util.h"

namespace netlist {

/// A class to represent a directed edge in a graph.
template<class NodeType, class EdgeType>
class DirectedEdge {
public:
    DirectedEdge(NodeType& sourceNode, NodeType& targetNode) :
        sourceNode(sourceNode), targetNode(targetNode) {}

    DirectedEdge<NodeType, EdgeType>& operator=(const DirectedEdge<NodeType, EdgeType>& edge) {
        sourceNode = edge.sourceNode;
        targetNode = edge.targetNode;
        return *this;
    }

    /// Static polymorphism: delegate implementation (via isEqualTo) to the
    /// derived class. Add friend operator to resolve ambiguity between operand
    /// ordering with C++20.
    friend bool operator==(const EdgeType& A, const EdgeType& B) noexcept {
        return A.getDerived().isEqualTo(B);
    }
    bool operator==(const EdgeType& E) const { return getDerived().isEqualTo(E); }

    /// Return the source node of this edge.
    NodeType& getSourceNode() const { return sourceNode; }

    /// Return the target node of this edge.
    NodeType& getTargetNode() const { return targetNode; }

protected:
    // As the default implementation use address comparison for equality.
    bool isEqualTo(const EdgeType& edge) const { return this == &edge; }

    // Cast the 'this' pointer to the derived type and return a reference.
    EdgeType& getDerived() { return *static_cast<EdgeType*>(this); }
    const EdgeType& getDerived() const { return *static_cast<const EdgeType*>(this); }

    NodeType& sourceNode;
    NodeType& targetNode;
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
    Node(EdgeType& edge) : edges() { edges.push_back(edge); }
    virtual ~Node() = default;

    const_iterator begin() const { return edges.begin(); }
    const_iterator end() const { return edges.end(); }
    iterator begin() { return edges.begin(); }
    iterator end() { return edges.end(); }

    Node<NodeType, EdgeType>& operator=(const Node<NodeType, EdgeType>& node) {
        edges = node.edges;
        return *this;
    }
    Node<NodeType, EdgeType>& operator=(Node<NodeType, EdgeType>&& node) noexcept {
        edges = std::move(node.edges);
        return *this;
    }

    /// Static polymorphism: delegate implementation (via isEqualTo) to the
    /// derived class. Add friend operator to resolve ambiguity between operand
    /// ordering with C++20.
    friend bool operator==(NodeType const& A, NodeType const& B) noexcept {
        return A.getDerived().isEqualTo(B);
    }
    bool operator==(const NodeType& N) const { return getDerived().isEqualTo(N); }

    /// Return an iterator to the edge connecting the target node.
    const_iterator findEdgeTo(const NodeType& targetNode) {
        return std::ranges::find_if(edges, [&targetNode](std::unique_ptr<EdgeType>& edge) {
            return edge->getTargetNode() == targetNode;
        });
    }

    /// Add an edge between this node and a target node, only if it does not
    /// already exist. Return a pointer to the newly-created edge.
    EdgeType& addEdge(NodeType& targetNode) {
        auto edgeIt = findEdgeTo(targetNode);
        if (edgeIt == edges.end()) {
            auto edge = std::make_unique<EdgeType>(getDerived(), targetNode);
            edges.emplace_back(std::move(edge));
            return *(edges.back().get());
        }
        else {
            return *((*edgeIt).get());
        }
    }

    /// Remove an edge between this node and a target node.
    /// Return true if the edge existed and was removed, and false otherwise.
    bool removeEdge(NodeType& targetNode) {
        auto edgeIt = findEdgeTo(targetNode);
        if (edgeIt != edges.end()) {
            edges.erase(edgeIt);
            return true;
        }
        else {
            return false;
        }
    }

    /// Populate a result vector of edges from this node to the specified target
    /// node. Return true if at least one edge was found.
    bool getEdgesTo(const NodeType& targetNode, std::vector<EdgeType*>& result) {
        SLANG_ASSERT(result.empty() && "Expected the results parameter to be empty");
        for (auto& edge : edges) {
            if (edge->getTargetNode() == targetNode) {
                result.push_back(edge.get());
            }
        }
        return !result.empty();
    }

    /// Return the list of outgoing edges from this node.
    const EdgeListType& getEdges() const { return edges; }

    /// Return the total number of edges outgoing from this node.
    size_t outDegree() const { return edges.size(); }

    /// Remove all edges outgoing from this node.
    void clearEdges() { edges.clear(); }

protected:
    // As the default implementation use address comparison for equality.
    bool isEqualTo(const NodeType& node) const { return this == &node; }
    // Cast the 'this' pointer to the derived type and return a reference.
    NodeType& getDerived() { return *static_cast<NodeType*>(this); }
    const NodeType& getDerived() const { return *static_cast<const NodeType*>(this); }

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

    node_descriptor findNode(const NodeType& nodeToFind) const {
        auto it = std::ranges::find_if(nodes, [&nodeToFind](const std::unique_ptr<NodeType>& node) {
            return const_cast<const NodeType&>(*node) == nodeToFind;
        });
        SLANG_ASSERT(it != nodes.end() && "Could not find node");
        return it - nodes.begin();
    }

    /// Given a node descriptor, return the node by reference.
    NodeType& getNode(node_descriptor node) const {
        SLANG_ASSERT(node < nodes.size() && "Node does not exist");
        return *nodes[node];
    }

    /// Add a node to the graph and return a reference to it.
    NodeType& addNode() {
        nodes.push_back(std::make_unique<NodeType>());
        return *(nodes.back().get());
    }

    /// Add an existing node to the graph and return a reference to it.
    NodeType& addNode(std::unique_ptr<NodeType> node) {
        nodes.push_back(std::move(node));
        return *(nodes.back().get());
    }

    /// Remove the specified node from the graph, including all edges that are
    /// incident upon this node, and all edges that are outgoing from this node.
    /// Return true if the node exists and was removed and false if it didn't
    /// exist.
    bool removeNode(NodeType& nodeToRemove) {
        auto nodeToRemoveDesc = findNode(nodeToRemove);
        if (nodeToRemoveDesc >= nodes.size()) {
            // The node is not in the graph.
            return false;
        }
        // Remove incoming edges to node for removal.
        std::vector<EdgeType*> edgesToRemove;
        for (auto& node : nodes) {
            if (nodeToRemove == *node) {
                // Skip the node to remove.
                continue;
            }
            node->getEdgesTo(nodeToRemove, edgesToRemove);
            for (auto* edge : edgesToRemove) {
                node->removeEdge(nodeToRemove);
            }
            edgesToRemove.clear();
        }
        // Remove the outgoing edges from the node for removal.
        nodeToRemove.clearEdges();
        // Remove the node itself.
        nodes.erase(std::ranges::next(nodes.begin(), nodeToRemoveDesc));
        return true;
    }

    /// Add an edge between two existing nodes in the graph.
    EdgeType& addEdge(NodeType& sourceNode, NodeType& targetNode) {
        SLANG_ASSERT(findNode(sourceNode) < nodes.size() && "Source node does not exist");
        SLANG_ASSERT(findNode(targetNode) < nodes.size() && "Target node does not exist");
        return sourceNode.addEdge(targetNode);
    }

    /// Remove an edge between the two specified vertices. Return true if the
    /// edge exists and was removed, and false if it didn't exist.
    bool removeEdge(NodeType& sourceNode, NodeType& targetNode) {
        SLANG_ASSERT(findNode(sourceNode) < nodes.size() && "Source node does not exist");
        SLANG_ASSERT(findNode(targetNode) < nodes.size() && "Target node does not exist");
        return sourceNode.removeEdge(targetNode);
    }

    /// Collect all edges that are incident to the specified node.
    /// Return true if at least one edge was found and false otherwise.
    bool getInEdgesToNode(const NodeType& targetNode, std::vector<EdgeType*>& results) const {
        SLANG_ASSERT(results.empty() && "Expected the results parameter to be empty");
        std::vector<EdgeType*> tempResults;
        for (auto& node : nodes) {
            node->getEdgesTo(targetNode, tempResults);
            results.insert(results.end(), tempResults.begin(), tempResults.end());
            tempResults.clear();
        }
        return !results.empty();
    }

    /// Return the number of edges eminating from the specified node.
    size_t outDegree(const NodeType& node) const {
        SLANG_ASSERT(findNode(node) < nodes.size() && "Node does not exist");
        return node.outDegree();
    }

    /// Return the number of edges incident to the specified node.
    size_t inDegree(const NodeType& node) const {
        std::vector<EdgeType*> results;
        getInEdgesToNode(node, results);
        return results.size();
    }

    /// Return the size of the graph.
    size_t numNodes() const { return nodes.size(); }

    /// Return the number of edges in the graph.
    size_t numEdges() const {
        size_t count = 0;
        for (auto& node : nodes) {
            count += node->outDegree();
        }
        return count;
    }

protected:
    NodeListType nodes;
};

} // namespace netlist
