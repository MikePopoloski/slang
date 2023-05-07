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
#include "SplitVariables.h"
#include "PathFinder.h"

using namespace netlist;

TEST_CASE("Simple example of a path through a module") {
  auto tree = SyntaxTree::fromText(R"(
module chain(input logic i_value,
             output logic o_value);

  assign o_value = i_value;

endmodule
)");
  Compilation compilation;
  compilation.addSyntaxTree(tree);
  NO_COMPILATION_ERRORS;
  Netlist netlist;
  NetlistVisitor visitor(compilation, netlist);
  compilation.getRoot().visit(visitor);
  SplitVariables splitVariables(netlist);
  CHECK(netlist.numNodes() == 6);
  CHECK(netlist.numEdges() == 5);
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
  // o_value -> i_value
  auto invalidPath = pathFinder.find(*outPort, *inPort);
  CHECK(invalidPath.empty());
}

TEST_CASE("Chain of 1-bit assignments in a sequence") {
  auto tree = SyntaxTree::fromText(R"(
module chain_sequence(input logic i_value,
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
  SplitVariables splitVariables(netlist);
  CHECK(netlist.numNodes() == 15);
  CHECK(netlist.numEdges() == 14);
  // Lookup the two ports in the netlist.
  auto *inPort = netlist.lookupPort("chain_sequence.i_value");
  CHECK(inPort != nullptr);
  auto *outPort = netlist.lookupPort("chain_sequence.o_value");
  CHECK(outPort != nullptr);
  // Setup the path finder.
  PathFinder pathFinder(netlist);
  // i_value -> o_value
  auto validPath = pathFinder.find(*inPort, *outPort);
  CHECK(!validPath.empty());
}

TEST_CASE("Chain of 1-bit assignments using an array") {
  auto tree = SyntaxTree::fromText(R"(
module chain(input logic i_value,
             output logic o_value);

  parameter p_stages = 4;

  logic pipeline [p_stages-1:0];

  assign pipeline[0] = i_value;

  always_comb begin
    for (int i=1; i<p_stages; i++) begin
      pipeline[i] = pipeline[i-1];
    end
  end

  assign o_value = pipeline[p_stages-1];

endmodule
)");
  Compilation compilation;
  compilation.addSyntaxTree(tree);
  NO_COMPILATION_ERRORS;
  Netlist netlist;
  NetlistVisitor visitor(compilation, netlist);
  compilation.getRoot().visit(visitor);
  SplitVariables splitVariables(netlist);
  CHECK(netlist.numNodes() == 20);
  CHECK(netlist.numEdges() == 25);
  // Lookup the two ports in the netlist.
  auto *inPort = netlist.lookupPort("chain.i_value");
  CHECK(inPort != nullptr);
  auto *outPort = netlist.lookupPort("chain.o_value");
  CHECK(outPort != nullptr);
  // Setup the path finder.
  PathFinder pathFinder(netlist);
  // i_value -> o_value, check it passes through each stage.
  auto validPath = pathFinder.find(*inPort, *outPort);
  CHECK(validPath.size() == 18);
}
