//------------------------------------------------------------------------------
//! @file DirectedGraphTest.cpp
//! @brief Directed graph ADT unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "CycleDetector.h"
#include "DirectedGraph.h"
#include "Test.h"
#include <fmt/format.h>

using namespace netlist;

namespace {

struct TestNode;
struct TestEdge;

struct TestNode : public Node<TestNode, TestEdge> {
    size_t id;
    TestNode(size_t id) : id(id) {};
};

struct TestEdge : public DirectedEdge<TestNode, TestEdge> {
    TestEdge(TestNode& sourceNode, TestNode& targetNode) : DirectedEdge(sourceNode, targetNode) {}
};

} // namespace

TEST_CASE("No cycles in graph") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& node0 = graph.addNode(std::make_unique<TestNode>(0));
    auto& node1 = graph.addNode(std::make_unique<TestNode>(1));
    auto& node2 = graph.addNode(std::make_unique<TestNode>(2));

    // Create edges: node1 -> node2 -> node3, no cycles
    graph.addEdge(node0, node1);
    graph.addEdge(node1, node2);

    CycleDetector<TestNode, TestEdge> detector(graph);
    auto cycles = detector.detectCycles();

    // No cycles should be present
    REQUIRE(cycles.empty());
}

TEST_CASE("Single cycle in the graph") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& node0 = graph.addNode(std::make_unique<TestNode>(0));
    auto& node1 = graph.addNode(std::make_unique<TestNode>(1));

    // Create edges: node1 -> node2 -> node1 (cycle between node1 and node2)
    graph.addEdge(node0, node1);
    graph.addEdge(node1, node0);

    CycleDetector<TestNode, TestEdge> detector(graph);
    auto cycles = detector.detectCycles();

    REQUIRE(cycles.size() == 1);    // One cycle should be detected
    REQUIRE(cycles[0].size() == 2); // Cycle contains two nodes
    // Cycle nodes match
    REQUIRE((cycles[0][0] == &node0 || cycles[0][0] == &node1));
    REQUIRE((cycles[0][1] == &node0 || cycles[0][1] == &node1));
}

TEST_CASE("Multiple cycles in the graph") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& node0 = graph.addNode(std::make_unique<TestNode>(0));
    auto& node1 = graph.addNode(std::make_unique<TestNode>(1));
    auto& node2 = graph.addNode(std::make_unique<TestNode>(2));
    auto& node3 = graph.addNode(std::make_unique<TestNode>(3));

    // Create cycles:
    //   node0 -> node1 -> node0
    //   node2 -> node3 -> node2
    graph.addEdge(node0, node1);
    graph.addEdge(node1, node0);
    graph.addEdge(node2, node3);
    graph.addEdge(node3, node2);

    CycleDetector<TestNode, TestEdge> detector(graph);
    auto cycles = detector.detectCycles();

    // Two separate cycles should be detected
    REQUIRE(cycles.size() == 2);

    // Verify details for cycle 1
    auto& cycle1 = cycles[0];
    REQUIRE(cycle1.size() == 2);
    REQUIRE((cycle1[0] == &node0 || cycle1[0] == &node1));
    REQUIRE((cycle1[1] == &node0 || cycle1[1] == &node1));

    // Verify details for cycle 2
    auto& cycle2 = cycles[1];
    REQUIRE(cycle2.size() == 2);
    REQUIRE((cycle2[0] == &node2 || cycle2[0] == &node3));
    REQUIRE((cycle2[1] == &node2 || cycle2[1] == &node3));
}

TEST_CASE("Graph with interconnected cycles") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& node0 = graph.addNode(std::make_unique<TestNode>(0));
    auto& node1 = graph.addNode(std::make_unique<TestNode>(1));
    auto& node2 = graph.addNode(std::make_unique<TestNode>(2));
    auto& node3 = graph.addNode(std::make_unique<TestNode>(3));

    // Create cycles:
    //   node0 -> node1 -> node2 -> node0
    //   node2 -> node3 -> node2
    graph.addEdge(node0, node1);
    graph.addEdge(node1, node2);
    graph.addEdge(node2, node0);
    graph.addEdge(node2, node3);
    graph.addEdge(node3, node2);

    CycleDetector<TestNode, TestEdge> detector(graph);
    auto cycles = detector.detectCycles();

    // Two separate cycles should be detected
    REQUIRE(cycles.size() == 2);

    // Verify details for cycle 1
    auto& cycle1 = cycles[0];
    REQUIRE(cycle1.size() == 3);
    REQUIRE((cycle1[0] == &node0 || cycle1[0] == &node1 || cycle1[0] == &node2));
    REQUIRE((cycle1[1] == &node0 || cycle1[1] == &node1 || cycle1[1] == &node2));
    REQUIRE((cycle1[2] == &node0 || cycle1[2] == &node1 || cycle1[2] == &node2));

    // Verify details for cycle 2
    auto& cycle2 = cycles[1];
    REQUIRE(cycle2.size() == 2);
    REQUIRE((cycle2[0] == &node2 || cycle2[0] == &node3));
    REQUIRE((cycle2[1] == &node2 || cycle2[1] == &node3));
}
