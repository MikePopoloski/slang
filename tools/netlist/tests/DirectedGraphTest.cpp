//------------------------------------------------------------------------------
//! @file DirectedGraphTest.cpp
//! @brief Directed graph ADT unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "Test.h"
#include "DirectedGraph.h"

TEST_CASE("Basic construction test") {

  struct TestNode;
  struct TestEdge;

  struct TestNode : public Node<TestNode, TestEdge> {
    TestNode() = default;
  };

  struct TestEdge : public DirectedEdge<TestNode, TestEdge> {
    TestEdge(TestNode &targetNode) : DirectedEdge(targetNode) {}
  };

  DirectedGraph<TestNode, TestEdge> graph;
  auto n0 = graph.addNode();
  auto n1 = graph.addNode();
  auto n2 = graph.addNode();
  auto n3 = graph.addNode();
  graph.addEdge(n0, n1);
  graph.addEdge(n0, n2);
  graph.addEdge(n0, n3);
  graph.addEdge(n1, n2);
  graph.addEdge(n1, n3);
  graph.addEdge(n2, n3);
  CHECK(graph.size() == 4);
  // Out edges.
  CHECK(graph.getNode(n0).outDegree() == 3);
  CHECK(graph.getNode(n1).outDegree() == 2);
  CHECK(graph.getNode(n2).outDegree() == 1);
  CHECK(graph.getNode(n3).outDegree() == 0);
  // In edges.
  CHECK(graph.inDegree(n0) == 0);
  CHECK(graph.inDegree(n1) == 1);
  CHECK(graph.inDegree(n2) == 2);
  CHECK(graph.inDegree(n3) == 3);
}

