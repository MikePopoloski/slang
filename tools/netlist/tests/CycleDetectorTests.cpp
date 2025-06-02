//------------------------------------------------------------------------------
//! @file DirectedGraphTest.cpp
//! @brief Directed graph ADT unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include <fmt/format.h>

#include "DirectedGraph.h"
#include "CycleDetector.h"
#include "Test.h"

using namespace netlist;

namespace {

struct TestNode;
struct TestEdge;

struct TestNode : public Node<TestNode, TestEdge> {
    TestNode() = default;
};

struct TestEdge : public DirectedEdge<TestNode, TestEdge> {
    TestEdge(TestNode& sourceNode, TestNode& targetNode) : DirectedEdge(sourceNode, targetNode) {}
};

} // namespace

TEST_CASE("No cycles in graph") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& node1 = graph.addNode();
    auto& node2 = graph.addNode();
    auto& node3 = graph.addNode();

    // Create edges: node1 -> node2, node2 -> node3, no cycles
    graph.addEdge(node1, node2);
    graph.addEdge(node2, node3);

    CycleDetector<TestNode, TestEdge> detector(graph);
    auto cycles = detector.detectCycles();

    fmt::print("num cycles={}\n", cycles.size());
    REQUIRE(cycles.empty()); // No cycles should be present
}
