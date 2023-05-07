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

TEST_CASE("Empty module") {
  // Test the simplest path can be traced through a module.
  auto tree = SyntaxTree::fromText(R"(
module empty (
  input logic i_value,
  output logic o_value);
endmodule
)");
  Compilation compilation;
  compilation.addSyntaxTree(tree);
  NO_COMPILATION_ERRORS;
  Netlist netlist;
  NetlistVisitor visitor(compilation, netlist);
  compilation.getRoot().visit(visitor);
  SplitVariables splitVariables(netlist);
  CHECK(netlist.numNodes() == 4);
  CHECK(netlist.numEdges() == 2);
}

TEST_CASE("Simplest path through a module") {
  // Test the simplest path can be traced through a module.
  auto tree = SyntaxTree::fromText(R"(
module passthrough (
  input logic i_value,
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
  auto *inPort = netlist.lookupPort("passthrough.i_value");
  CHECK(inPort != nullptr);
  auto *outPort = netlist.lookupPort("passthrough.o_value");
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

TEST_CASE("Chain of assignments in a sequence") {
  // Test that correct dependencies can be formed from procedural and
  // continuous assignments.
  auto tree = SyntaxTree::fromText(R"(
module chain_sequence (
  input logic i_value,
  output logic o_value);

  logic a, b, c, d, e;

  assign a = i_value;

  always_comb begin
    b = a;
    c = b;
    d = c;
  end

  assign e = d;
  assign o_value = e;

endmodule
)");
  Compilation compilation;
  compilation.addSyntaxTree(tree);
  NO_COMPILATION_ERRORS;
  Netlist netlist;
  NetlistVisitor visitor(compilation, netlist);
  compilation.getRoot().visit(visitor);
  SplitVariables splitVariables(netlist);
  CHECK(netlist.numNodes() == 21);
  CHECK(netlist.numEdges() == 20);
  // Lookup the two ports in the netlist.
  auto *inPort = netlist.lookupPort("chain_sequence.i_value");
  CHECK(inPort != nullptr);
  auto *outPort = netlist.lookupPort("chain_sequence.o_value");
  CHECK(outPort != nullptr);
  // Setup the path finder.
  PathFinder pathFinder(netlist);
  // i_value -> o_value
  auto validPath = pathFinder.find(*inPort, *outPort);
  CHECK(validPath.size() == 21);
}

TEST_CASE("Chain of assignments using an array") {
  // Test that variable declarations can be split out for elements of an array.
  auto tree = SyntaxTree::fromText(R"(
module chain_array #(parameter N=4) (
  input logic i_value,
  output logic o_value);

  logic pipeline [N-1:0];

  assign pipeline[0] = i_value;

  always_comb begin
    for (int i=1; i<N; i++) begin
      pipeline[i] = pipeline[i-1];
    end
  end

  assign o_value = pipeline[N-1];

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
  auto *inPort = netlist.lookupPort("chain_array.i_value");
  CHECK(inPort != nullptr);
  auto *outPort = netlist.lookupPort("chain_array.o_value");
  CHECK(outPort != nullptr);
  // Setup the path finder.
  PathFinder pathFinder(netlist);
  // i_value -> o_value, check it passes through each stage.
  auto validPath = pathFinder.find(*inPort, *outPort);
  CHECK(validPath.size() == 18);
}

TEST_CASE("Chain of assignments using nested for loops") {
  // Expand the previous test to check the handling of multiple loop variables.
  auto tree = SyntaxTree::fromText(R"(
module chain_nested #(parameter N=3) (
  input logic i_value,
  output logic o_value);

  logic [(N*N)-1:0] stages;

  //assign stages[0] = i_value;
  assign o_value = stages[(N*N)-1];

  always_comb begin
    for (int i=0; i<N; i++) begin
      for (int j=0; j<N; j++) begin
        if ((i == 0) && (j == 0))
          stages[0] = i_value;
        else
          stages[(i*N + j)] = stages[(i*N + j)-1];
      end
    end
  end

endmodule
)");
  Compilation compilation;
  compilation.addSyntaxTree(tree);
  NO_COMPILATION_ERRORS;
  Netlist netlist;
  NetlistVisitor visitor(compilation, netlist);
  compilation.getRoot().visit(visitor);
  SplitVariables splitVariables(netlist);
  CHECK(netlist.numNodes() == 36);
  CHECK(netlist.numEdges() == 50);
  // Lookup the two ports in the netlist.
  auto *inPort = netlist.lookupPort("chain_nested.i_value");
  CHECK(inPort != nullptr);
  auto *outPort = netlist.lookupPort("chain_nested.o_value");
  CHECK(outPort != nullptr);
  // Setup the path finder.
  PathFinder pathFinder(netlist);
  // i_value -> o_value, check it passes through each stage.
  auto validPath = pathFinder.find(*inPort, *outPort);
  CHECK(validPath.size() == 33);
}

TEST_CASE("Two chains of assignments using a shared 2D array") {
  // Check that assignments corresponding to two distinct paths, using the same
  // array variable can be handled.
  auto tree = SyntaxTree::fromText(R"(
module chain_loop_dual #(parameter N=4)(
  input logic i_value_a,
  input logic i_value_b,
  output logic o_value_a,
  output logic o_value_b
);

  parameter A = 0;
  parameter B = 1;

  logic pipeline [1:0][N-1:0];

  assign pipeline[A][0] = i_value_a;
  assign pipeline[B][0] = i_value_b;

  always_comb begin
    for (int i=1; i<N; i++) begin
      pipeline[A][i] = pipeline[A][i-1];
      pipeline[B][i] = pipeline[B][i-1];
    end
  end

  assign o_value_a = pipeline[A][N-1];
  assign o_value_b = pipeline[B][N-1];

endmodule
)");
  Compilation compilation;
  compilation.addSyntaxTree(tree);
  NO_COMPILATION_ERRORS;
  Netlist netlist;
  NetlistVisitor visitor(compilation, netlist);
  compilation.getRoot().visit(visitor);
  SplitVariables splitVariables(netlist);
  // Lookup the two ports in the netlist.
  auto *inPortA = netlist.lookupPort("chain_loop_dual.i_value_a");
  CHECK(inPortA != nullptr);
  auto *inPortB = netlist.lookupPort("chain_loop_dual.i_value_b");
  CHECK(inPortB != nullptr);
  auto *outPortA = netlist.lookupPort("chain_loop_dual.o_value_a");
  CHECK(outPortA != nullptr);
  auto *outPortB = netlist.lookupPort("chain_loop_dual.o_value_b");
  CHECK(outPortB != nullptr);
  // Setup the path finder.
  PathFinder pathFinder(netlist);
  // i_value_a -> o_value_a
  CHECK(pathFinder.find(*inPortA, *outPortA).size() == 18);
  // i_value_b -> o_value_b
  CHECK(pathFinder.find(*inPortB, *outPortB).size() == 18);
  // Invalid paths.
  CHECK(pathFinder.find(*inPortA, *outPortB).empty());
  CHECK(pathFinder.find(*inPortB, *outPortA).empty());
}
