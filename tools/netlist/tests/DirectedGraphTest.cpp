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

  DirectedGraph<int, int> graph;
  graph.addNode(0);

  CHECK(true);
}

