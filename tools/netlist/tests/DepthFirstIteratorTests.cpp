//------------------------------------------------------------------------------
//! @file DepthFirstIteratorTest.cpp
//! @brief Depth-first iterator unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "Test.h"
#include "DirectedGraph.h"
#include "DepthFirstIterator.h"

struct TestNode;
struct TestEdge;

struct TestNode : public Node<TestNode, TestEdge> {
  TestNode() = default;
};

struct TestEdge : public DirectedEdge<TestNode, TestEdge> {
  TestEdge(TestNode &targetNode) : DirectedEdge(targetNode) {}
};

TEST_CASE("Depth first iterator") {
  DirectedGraph<TestNode, TestEdge> graph;
  auto &n0 = graph.addNode();
  auto &n1 = graph.addNode();
  auto &n2 = graph.addNode();
  graph.addEdge(n0, n1);
  graph.addEdge(n1, n2);
  graph.addEdge(n2, n0);
  std::vector<TestNode*> path;
  for (auto it = DepthFirstIterator<TestNode, TestEdge>::begin(n0),
            itEnd = DepthFirstIterator<TestNode, TestEdge>::end();
       it != itEnd; it++) {
    path.push_back(&*it);
  }
  CHECK(*path[0] == n0);
  CHECK(*path[1] == n1);
  CHECK(*path[2] == n2);
}
