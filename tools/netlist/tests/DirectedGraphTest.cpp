//------------------------------------------------------------------------------
//! @file DirectedGraphTest.cpp
//! @brief Directed graph ADT unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "Test.h"
#include "DirectedGraph.h"

TEST_CASE("Basic connectivity test") {

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
  graph.addEdge(n0, n1);
  graph.addEdge(n0, n2);
  CHECK(true);
}

