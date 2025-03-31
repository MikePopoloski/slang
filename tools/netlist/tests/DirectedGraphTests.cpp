//------------------------------------------------------------------------------
//! @file DirectedGraphTest.cpp
//! @brief Directed graph ADT unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "DirectedGraph.h"
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

TEST_CASE("Test node and edge equality") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& n0 = graph.addNode();
    auto& n0Alias = graph.getNode(graph.findNode(n0));
    CHECK(n0 == n0Alias);
    auto& n1 = graph.addNode();
    CHECK(n0 != n1);
    auto& n2 = graph.addNode();
    auto& e0 = n0.addEdge(n1);
    auto& e1 = n1.addEdge(n2);
    auto* e0Alias = n0.findEdgeTo(n1)->get();
    CHECK(e0 == *e0Alias);
    CHECK(e0 != e1);
}

TEST_CASE("Test basic connectivity") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& n0 = graph.addNode();
    auto& n1 = graph.addNode();
    auto& n2 = graph.addNode();
    auto& n3 = graph.addNode();
    CHECK(graph.numNodes() == 4);
    CHECK(graph.numEdges() == 0);
    auto& e0 = graph.addEdge(n0, n1);
    auto& e1 = graph.addEdge(n0, n2);
    auto& e2 = graph.addEdge(n0, n3);
    auto& e3 = graph.addEdge(n1, n2);
    auto& e4 = graph.addEdge(n1, n3);
    auto& e5 = graph.addEdge(n2, n3);
    CHECK(graph.numEdges() == 6);
    // Edge target nodes.
    CHECK(e0.getTargetNode() == n1);
    CHECK(e1.getTargetNode() == n2);
    CHECK(e2.getTargetNode() == n3);
    CHECK(e3.getTargetNode() == n2);
    CHECK(e4.getTargetNode() == n3);
    CHECK(e5.getTargetNode() == n3);
    // Edge source nodes.
    CHECK(e0.getSourceNode() == n0);
    CHECK(e1.getSourceNode() == n0);
    CHECK(e2.getSourceNode() == n0);
    CHECK(e3.getSourceNode() == n1);
    CHECK(e4.getSourceNode() == n1);
    CHECK(e5.getSourceNode() == n2);
    // Out degrees.
    CHECK(graph.outDegree(n0) == 3);
    CHECK(graph.outDegree(n1) == 2);
    CHECK(graph.outDegree(n2) == 1);
    CHECK(graph.outDegree(n3) == 0);
    CHECK(n0.outDegree() == 3);
    CHECK(n1.outDegree() == 2);
    CHECK(n2.outDegree() == 1);
    CHECK(n3.outDegree() == 0);
    // In degrees.
    CHECK(graph.inDegree(n0) == 0);
    CHECK(graph.inDegree(n1) == 1);
    CHECK(graph.inDegree(n2) == 2);
    CHECK(graph.inDegree(n3) == 3);
}

TEST_CASE("Test removing nodes") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& n0 = graph.addNode();
    auto& n1 = graph.addNode();
    auto& n2 = graph.addNode();
    // Create a ring of n0, n1, n2
    graph.addEdge(n0, n1);
    graph.addEdge(n1, n2);
    graph.addEdge(n2, n0);
    CHECK(graph.numNodes() == 3);
    CHECK(graph.numEdges() == 3);
    // Remove n0
    CHECK(graph.removeNode(n0));
    CHECK(graph.inDegree(n1) == 0);
    CHECK(graph.outDegree(n1) == 1);
    CHECK(graph.inDegree(n2) == 1);
    CHECK(graph.outDegree(n2) == 0);
    // Remoe n1
    CHECK(graph.removeNode(n1));
    CHECK(graph.inDegree(n2) == 0);
    CHECK(graph.outDegree(n2) == 0);
    // Remove n2
    CHECK(graph.removeNode(n2));
    CHECK(graph.numNodes() == 0);
}

TEST_CASE("Test removing edges") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& n0 = graph.addNode();
    auto& n1 = graph.addNode();
    auto& n2 = graph.addNode();
    // Create a ring of n0 -e0- n1 -e1- n2 -e2-
    graph.addEdge(n0, n1); // e0
    graph.addEdge(n1, n2); // e1
    graph.addEdge(n2, n0); // e2
    CHECK(graph.numNodes() == 3);
    CHECK(graph.numEdges() == 3);
    // Remove e0.
    CHECK(graph.removeEdge(n0, n1));
    CHECK(graph.outDegree(n0) == 0);
    CHECK(graph.inDegree(n1) == 0);
    // Remove e1.
    CHECK(graph.removeEdge(n1, n2));
    CHECK(graph.outDegree(n1) == 0);
    CHECK(graph.inDegree(n2) == 0);
    // Remove e2.
    CHECK(graph.removeEdge(n2, n0));
    CHECK(graph.outDegree(n2) == 0);
    CHECK(graph.inDegree(n0) == 0);
    // Edges no longer exist
    CHECK(!graph.removeEdge(n0, n1));
    CHECK(!graph.removeEdge(n1, n2));
    CHECK(!graph.removeEdge(n2, n0));
}

TEST_CASE("Test iterating over nodes and node's edges") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& n0 = graph.addNode();
    auto& n1 = graph.addNode();
    auto& n2 = graph.addNode();
    auto& n3 = graph.addNode();
    graph.addEdge(n0, n1);
    graph.addEdge(n0, n2);
    graph.addEdge(n0, n3);
    // Nodes.
    {
        size_t count = 0;
        for (auto it = graph.begin(); it != graph.end(); it++) {
            count++;
        }
        CHECK(count == 4);
    }
    // n0 edges.
    {
        size_t count = 0;
        for (auto it = n0.begin(); it != n0.end(); it++) {
            count++;
        }
        CHECK(count == 3);
    }
    // n1 edges.
    {
        size_t count = 0;
        for (auto it = n1.begin(); it != n1.end(); it++) {
            count++;
        }
        CHECK(count == 0);
    }
}
