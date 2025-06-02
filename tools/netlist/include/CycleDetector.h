#pragma once

#include "DirectedGraph.h"
#include "DepthFirstSearch.h"
#include <vector>
#include <unordered_set>

namespace netlist {

/// Visitor class for identifying cycles during Depth-First Search.
template<class NodeType, class EdgeType>
class CycleDetectionVisitor {
public:
    /// Called when visiting a node during DFS traversal.
    void visitNode(const NodeType& node) {
        recursionStack.push_back(&node);
    }

    /// Called when visiting an edge during DFS traversal.
    void visitEdge(const EdgeType& edge) {
        auto& targetNode = edge.getTargetNode();

        // Detect cycle: targetNode is part of the current recursion stack
        auto cycleStart = std::find(recursionStack.begin(), recursionStack.end(), &targetNode);
        if (cycleStart != recursionStack.end()) {
            // Extract cycle nodes
            std::vector<const NodeType*> cycleNodes(cycleStart, recursionStack.end());
            cycles.emplace_back(std::move(cycleNodes));
        }
    }

    /// Called when backtracking a node (after processing all edges).
    void backtrackNode(const NodeType& node) {
        recursionStack.pop_back();
    }

    /// Returns all detected cycles.
    const std::vector<std::vector<const NodeType*>>& getCycles() const {
        return cycles;
    }

private:
    std::vector<const NodeType*> recursionStack;
    std::vector<std::vector<const NodeType*>> cycles;
};

/// Class for reporting all cycles in a directed graph.
template<class NodeType, class EdgeType>
class CycleDetector {
public:
    explicit CycleDetector(const DirectedGraph<NodeType, EdgeType>& graph) : graph(graph) {}

    /// Detect all cycles within the graph.
    /// Returns a vector containing cycles, where each cycle is represented as a vector of nodes.
    std::vector<std::vector<const NodeType*>> detectCycles() {
        CycleDetectionVisitor<NodeType, EdgeType> visitor;

        // Start a DFS traversal from each node
        for (const auto& nodePtr : graph) {
            if (visitedNodes.count(nodePtr.get()) == 0) {
                DepthFirstSearch<NodeType, EdgeType, CycleDetectionVisitor<NodeType, EdgeType>> dfs(visitor, *nodePtr);
                markAllVisitedNodes(visitor);
            }
        }

        return visitor.getCycles();
    }

private:
    const DirectedGraph<NodeType, EdgeType>& graph;
    std::unordered_set<const NodeType*> visitedNodes;

    void markAllVisitedNodes(CycleDetectionVisitor<NodeType, EdgeType>& visitor) {
        for (const auto& cycle : visitor.getCycles()) {
            for (const auto node : cycle) {
                visitedNodes.insert(node);
            }
        }
    }
};

} // namespace netlist
