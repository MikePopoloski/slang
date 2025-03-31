//------------------------------------------------------------------------------
//! @file DepthFirstSearchTests.cpp
//! @brief Depth-first search unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "DepthFirstSearch.h"
#include "DirectedGraph.h"
#include "Test.h"

using namespace netlist;

namespace {

struct TestNode;
struct TestEdge;

size_t nodeIDs = 0;

struct TestNode : public Node<TestNode, TestEdge> {
    size_t ID;
    TestNode() : ID(nodeIDs++) {};
};

struct TestEdge : public DirectedEdge<TestNode, TestEdge> {
    TestEdge(TestNode& sourceNode, TestNode& targetNode) : DirectedEdge(sourceNode, targetNode) {}
};

struct TestVisitor {
    std::vector<TestNode*> nodes;
    std::vector<TestEdge*> edges;
    TestVisitor() = default;
    void visitNode(TestNode& node) { nodes.push_back(&node); };
    void visitEdge(TestEdge& edge) { edges.push_back(&edge); };
};

} // namespace

TEST_CASE("Depth-first search on a ring") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& n0 = graph.addNode();
    auto& n1 = graph.addNode();
    auto& n2 = graph.addNode();
    auto& n3 = graph.addNode();
    auto& n4 = graph.addNode();
    graph.addEdge(n0, n1);
    graph.addEdge(n1, n2);
    graph.addEdge(n2, n3);
    graph.addEdge(n3, n4);
    graph.addEdge(n4, n0);
    TestVisitor visitor;
    DepthFirstSearch<TestNode, TestEdge, TestVisitor> dfs(visitor, n3);
    CHECK(visitor.nodes.size() == 5);
    CHECK(visitor.edges.size() == 4);
    CHECK(*visitor.nodes[0] == n3);
    CHECK(*visitor.nodes[1] == n4);
    CHECK(*visitor.nodes[2] == n0);
    CHECK(*visitor.nodes[3] == n1);
    CHECK(*visitor.nodes[4] == n2);
}

TEST_CASE("Depth-first search on a tree") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& n0 = graph.addNode();
    auto& n1 = graph.addNode();
    auto& n2 = graph.addNode();
    auto& n3 = graph.addNode();
    auto& n4 = graph.addNode();
    auto& n5 = graph.addNode();
    auto& n6 = graph.addNode();
    graph.addEdge(n0, n1);
    graph.addEdge(n0, n2);
    graph.addEdge(n1, n3);
    graph.addEdge(n1, n4);
    graph.addEdge(n2, n5);
    graph.addEdge(n2, n6);
    TestVisitor visitor;
    DepthFirstSearch<TestNode, TestEdge, TestVisitor> dfs(visitor, n0);
    CHECK(visitor.nodes.size() == 7);
    CHECK(visitor.edges.size() == 6);
    CHECK(*visitor.nodes[0] == n0);
    CHECK(*visitor.nodes[1] == n1);
    CHECK(*visitor.nodes[2] == n3);
    CHECK(*visitor.nodes[3] == n4);
    CHECK(*visitor.nodes[4] == n2);
    CHECK(*visitor.nodes[5] == n5);
    CHECK(*visitor.nodes[6] == n6);
}

// A predicate to select edges that only connect nodes with even IDs.
struct EdgesToOnlyEvenNodes {
    EdgesToOnlyEvenNodes() = default;
    bool operator()(const TestEdge& edge) { return edge.getTargetNode().ID % 2 == 0; }
};

TEST_CASE("Depth-first search with an edge predicate") {
    DirectedGraph<TestNode, TestEdge> graph;
    auto& n0 = graph.addNode();
    auto& n1 = graph.addNode();
    auto& n2 = graph.addNode();
    auto& n3 = graph.addNode();
    auto& n4 = graph.addNode();
    // Fan out n0 to all other nodes.
    graph.addEdge(n0, n1);
    graph.addEdge(n0, n2);
    graph.addEdge(n0, n3);
    graph.addEdge(n0, n4);
    TestVisitor visitor;
    DepthFirstSearch<TestNode, TestEdge, TestVisitor, EdgesToOnlyEvenNodes> dfs(visitor, n0);
    CHECK(visitor.nodes.size() == 3);
    CHECK(visitor.edges.size() == 2);
    CHECK(*visitor.nodes[0] == n0);
    CHECK(*visitor.nodes[1] == n2);
    CHECK(*visitor.nodes[2] == n4);
}
