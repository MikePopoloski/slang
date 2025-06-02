#pragma once

#include "DepthFirstSearch.h"
#include "DirectedGraph.h"
#include <unordered_set>
#include <vector>

namespace netlist {

/// Visitor class for identifying cycles during Depth-First Search.
template<class NodeType, class EdgeType>
struct CycleDetectionVisitor {

    void visitedNode(const NodeType& node) {
        // Detect cycle: targetNode is part of the current recursion stack
        auto cycleStart = std::find(recursionStack.begin(), recursionStack.end(), &node);
        if (cycleStart != recursionStack.end()) {
            // Extract cycle nodes
            std::vector<const NodeType*> cycleNodes(cycleStart, recursionStack.end());
            cycles.emplace_back(std::move(cycleNodes));
        }
    }

    void visitNode(const NodeType& node) { 
        recursionStack.push_back(&node);
    }

    void visitEdge(const EdgeType& edge) {}

    /// Returns all detected cycles.
    const std::vector<std::vector<const NodeType*>>& getCycles() const { return cycles; }

    std::vector<const NodeType*> recursionStack;
    std::vector<std::vector<const NodeType*>> cycles;
};

/// Class for reporting all cycles in a directed graph.
template<class NodeType, class EdgeType, class EdgePredicate = select_all>
class CycleDetector {
public:
    explicit CycleDetector(const DirectedGraph<NodeType, EdgeType>& graph) : graph(graph) {}

    /// Detect all cycles within the graph.
    /// Returns a vector containing cycles, where each cycle is represented as a vector of nodes.
    auto detectCycles() {
      std::vector<std::vector<const NodeType*>> cycles;

        // Start a DFS traversal from each node
        for (const auto& nodePtr : graph) {
            CycleDetectionVisitor<NodeType, EdgeType> visitor;
            const auto* startNode = nodePtr.get();
            if (visitedNodes.count(startNode) == 0) {

                // Mark the starting node as visited.
                visitedNodes.insert(startNode);

                // Perform DFS traversal.
                DepthFirstSearch<NodeType, EdgeType, CycleDetectionVisitor<NodeType, EdgeType>,
                                 EdgePredicate>
                    dfs(visitor, *nodePtr);

                // Additionally, mark all nodes in cycles as visited to avoid
                // redundant DFS calls.
                markAllVisitedNodes(visitor);
            }

            // Add any cycles that were found.
            cycles.insert(cycles.end(), visitor.cycles.begin(), visitor.cycles.end());
        }

        return cycles;
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
