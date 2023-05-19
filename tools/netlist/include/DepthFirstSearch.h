//------------------------------------------------------------------------------
//! @file DepthFirstSearch.h
//! @brief Implementation of depth-first search on a directed graph.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "DirectedGraph.h"
#include <set>
#include <vector>

namespace netlist {

struct select_all {
    template<typename T>
    bool operator()(const T&) const {
        return true;
    }
};

/// Depth-first search on a directed graph. A visitor class provides visibility
/// to the caller of visits to edges and nodes. An optional edge predicate
/// selects which edges can be included in the traversal.
template<class NodeType, class EdgeType, class Visitor, class EdgePredicate = select_all>
class DepthFirstSearch {
public:
    DepthFirstSearch(Visitor& visitor, NodeType& startNode) : visitor(visitor) {
        setup(startNode);
        run();
    }

    DepthFirstSearch(Visitor& visitor, EdgePredicate edgePredicate, NodeType& startNode) :
        visitor(visitor), edgePredicate(edgePredicate) {
        setup(startNode);
        run();
    }

private:
    using EdgeIteratorType = typename NodeType::iterator;
    using VisitStackElement = std::pair<NodeType&, EdgeIteratorType>;

    /// Setup the traversal.
    void setup(NodeType& startNode) {
        visitedNodes.insert(&startNode);
        visitStack.push_back(VisitStackElement(startNode, startNode.begin()));
        visitor.visitNode(startNode);
    }

    /// Perform a depth-first traversal, calling the visitor methods on the way.
    void run() {
        while (!visitStack.empty()) {
            auto& node = visitStack.back().first;
            auto& nodeIt = visitStack.back().second;
            // Visit each child node that hasn't already been visited.
            while (nodeIt != node.end()) {
                auto* edge = nodeIt->get();
                auto& targetNode = edge->getTargetNode();
                nodeIt++;
                if (edgePredicate(*edge) && visitedNodes.count(&targetNode) == 0) {
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
    Visitor& visitor;
    EdgePredicate edgePredicate;
    std::set<const NodeType*> visitedNodes;
    std::vector<VisitStackElement> visitStack;
};

} // namespace netlist
