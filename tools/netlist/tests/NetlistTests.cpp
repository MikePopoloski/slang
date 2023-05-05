//------------------------------------------------------------------------------
//! @file NetlistTest.cpp
//! @brief Netlist unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "Test.h"
#include "Netlist.h"
#include "NetlistVisitor.h"
#include "PathFinder.h"

using namespace netlist;

TEST_CASE("Chain of 1-bit assignments") {
  auto tree = SyntaxTree::fromText(R"(
module chain(input logic i_value,
             output logic o_value);

  logic a, b, c;

  always_comb begin
    a = i_value;
    b = a;
    c = b;
  end

  assign o_value = c;

endmodule
)");
  Compilation compilation;
  compilation.addSyntaxTree(tree);
  NO_COMPILATION_ERRORS;
  Netlist netlist;
  NetlistVisitor visitor(compilation, netlist);
  compilation.getRoot().visit(visitor);
  CHECK(netlist.numNodes() == 15);
  CHECK(netlist.numEdges() == 14);
  // Lookup the two ports in the netlist.
  auto *inPort = netlist.lookupPort("chain.i_value");
  CHECK(inPort != nullptr);
  auto *outPort = netlist.lookupPort("chain.o_value");
  CHECK(outPort != nullptr);
  // Setup the path finder.
  PathFinder pathFinder(netlist);
  // i_value -> o_value
  auto validPath = pathFinder.find(*inPort, *outPort);
  CHECK(!validPath.empty());
  // i_value -> o_value
  auto invalidPath = pathFinder.find(*outPort, *inPort);
  CHECK(invalidPath.empty());
}
