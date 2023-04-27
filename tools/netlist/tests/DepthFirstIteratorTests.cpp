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

using namespace netlist;

struct TestNode;
struct TestEdge;

size_t nodeIDs = 0;

struct TestNode : public Node<TestNode, TestEdge> {
  size_t ID;
  TestNode() : ID(nodeIDs++) {};
};

struct TestEdge : public DirectedEdge<TestNode, TestEdge> {
  TestEdge(TestNode &sourceNode, TestNode &targetNode) : DirectedEdge(sourceNode, targetNode) {}
};

TEST_CASE("Depth-first iteration on a ring") {
  DirectedGraph<TestNode, TestEdge> graph;
  auto &n0 = graph.addNode();
  auto &n1 = graph.addNode();
  auto &n2 = graph.addNode();
  auto &n3 = graph.addNode();
  graph.addEdge(n0, n1);
  graph.addEdge(n1, n2);
  graph.addEdge(n2, n3);
  graph.addEdge(n3, n0);
  std::vector<TestNode*> nodes({&n0});
  std::vector<TestEdge*> edges;
  for (auto it = DepthFirstIterator<TestNode, TestEdge>::begin(n0),
            end = DepthFirstIterator<TestNode, TestEdge>::end();
       it != end; it++) {
    auto edge = *it;
    std::cout<<"NODE "<<edge.getTargetNode().ID<< "\n";
    nodes.push_back(&edge.getTargetNode());
    edges.push_back(&edge);
  }
  CHECK(nodes.size() == 4);
  CHECK(edges.size() == 3);
  CHECK(*nodes[0] == n0);
  CHECK(*nodes[1] == n1);
  CHECK(*nodes[2] == n2);
  CHECK(*nodes[3] == n3);
}

//TEST_CASE("Depth-first iteraton on a tree") {
//  DirectedGraph<TestNode, TestEdge> graph;
//  auto &n0 = graph.addNode();
//  auto &n1 = graph.addNode();
//  auto &n2 = graph.addNode();
//  auto &n3 = graph.addNode();
//  auto &n4 = graph.addNode();
//  auto &n5 = graph.addNode();
//  auto &n6 = graph.addNode();
//  graph.addEdge(n0, n1);
//  graph.addEdge(n0, n2);
//  graph.addEdge(n1, n3);
//  graph.addEdge(n1, n4);
//  graph.addEdge(n2, n5);
//  graph.addEdge(n2, n6);
//  std::vector<TestNode*> nodes;
//  std::vector<TestEdge*> edges;
//  for (auto it = DepthFirstIterator<TestNode, TestEdge>::begin(n0),
//            itEnd = DepthFirstIterator<TestNode, TestEdge>::end();
//       it != itEnd; it++) {
//    auto edge = *it;
//    nodes.push_back(&edge.getTargetNode());
//    edges.push_back(&edge);
//  }
//  CHECK(nodes.size() == 7);
//  CHECK(edges.size() == 6);
//  CHECK(*nodes[0] == n0);
//  CHECK(*nodes[1] == n1);
//  CHECK(*nodes[2] == n2);
//  CHECK(*nodes[3] == n3);
//  CHECK(*nodes[4] == n4);
//  CHECK(*nodes[5] == n5);
//  CHECK(*nodes[6] == n6);
//}
//
