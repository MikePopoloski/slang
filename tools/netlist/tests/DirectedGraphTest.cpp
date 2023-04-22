//------------------------------------------------------------------------------
//! @file DirectedGraphTest.cpp
//! @brief Directed graph ADT unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "Test.h"
#include "DirectedGraph.h"

struct TestNode;
struct TestEdge;

struct TestNode : public Node<TestNode, TestEdge> {
  TestNode() = default;
};

struct TestEdge : public DirectedEdge<TestNode, TestEdge> {
  TestEdge(TestNode &targetNode) : DirectedEdge(targetNode) {}
};

TEST_CASE("Test basic connectivity") {
  DirectedGraph<TestNode, TestEdge> graph;
  auto &n0 = graph.addNode();
  auto &n1 = graph.addNode();
  auto &n2 = graph.addNode();
  auto &n3 = graph.addNode();
  CHECK(graph.numNodes() == 4);
  CHECK(graph.numEdges() == 0);
  auto &e0 = graph.addEdge(n0, n1);
  auto &e1 = graph.addEdge(n0, n2);
  auto &e2 = graph.addEdge(n0, n3);
  auto &e3 = graph.addEdge(n1, n2);
  auto &e4 = graph.addEdge(n1, n3);
  auto &e5 = graph.addEdge(n2, n3);
  CHECK(graph.numEdges() == 6);
  // Edge target nodes.
  CHECK(e0.getTargetNode() == n1);
  CHECK(e1.getTargetNode() == n2);
  CHECK(e2.getTargetNode() == n3);
  CHECK(e3.getTargetNode() == n2);
  CHECK(e4.getTargetNode() == n3);
  CHECK(e5.getTargetNode() == n3);
  // Out edges.
  CHECK(graph.outDegree(n0) == 3);
  CHECK(graph.outDegree(n1) == 2);
  CHECK(graph.outDegree(n2) == 1);
  CHECK(graph.outDegree(n3) == 0);
  // In edges.
  CHECK(graph.inDegree(n0) == 0);
  CHECK(graph.inDegree(n1) == 1);
  CHECK(graph.inDegree(n2) == 2);
  CHECK(graph.inDegree(n3) == 3);
}

TEST_CASE("Test removing nodes") {
  DirectedGraph<TestNode, TestEdge> graph;
  auto &n0 = graph.addNode();
  auto &n1 = graph.addNode();
  auto &n2 = graph.addNode();
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
  auto &n0 = graph.addNode();
  auto &n1 = graph.addNode();
  auto &n2 = graph.addNode();
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
