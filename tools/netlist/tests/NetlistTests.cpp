//------------------------------------------------------------------------------
//! @file NetlistTest.cpp
//! @brief Netlist unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "Netlist.h"
#include "NetlistVisitor.h"
#include "PathFinder.h"
#include "SplitVariables.h"
#include "Test.h"

using namespace netlist;

Netlist createNetlist(Compilation& compilation) {
    Netlist netlist;
    NetlistVisitor visitor(compilation, netlist);
    compilation.getRoot().visit(visitor);
    SplitVariables splitVariables(netlist);
    return netlist;
}

//===---------------------------------------------------------------------===//
// Basic tests
//===---------------------------------------------------------------------===//

TEST_CASE("Empty module") {
    // Test the simplest path can be traced through a module.
    auto tree = SyntaxTree::fromText(R"(
module empty (input logic i_value, output logic o_value);
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(netlist.numNodes() == 4);
    CHECK(netlist.numEdges() == 2);
    // Lookup the two ports in the netlist.
    auto* inPort = netlist.lookupPort("empty.i_value");
    CHECK(inPort != nullptr);
    auto* outPort = netlist.lookupPort("empty.o_value");
    CHECK(outPort != nullptr);
}

TEST_CASE("Pass through a module") {
    // Test the simplest path through a module.
    auto tree = SyntaxTree::fromText(R"(
module passthrough (input logic i_value, output logic o_value);
  assign o_value = i_value;
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(netlist.numNodes() == 6);
    CHECK(netlist.numEdges() == 5);
    // Lookup the two ports in the netlist.
    auto* inPort = netlist.lookupPort("passthrough.i_value");
    CHECK(inPort != nullptr);
    auto* outPort = netlist.lookupPort("passthrough.o_value");
    CHECK(outPort != nullptr);
    PathFinder pathFinder(netlist);
    // Valid i_value -> o_value
    CHECK(!pathFinder.find(*inPort, *outPort).empty());
    // Invalid o_value -> i_value
    CHECK(pathFinder.find(*outPort, *inPort).empty());
}

TEST_CASE("Chain of assignments in a sequence using variables") {
    // Test that correct dependencies can be formed from procedural and
    // continuous assignments.
    auto tree = SyntaxTree::fromText(R"(
module chain_vars (input logic i_value, output logic o_value);

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
    auto netlist = createNetlist(compilation);
    CHECK(netlist.numNodes() == 21);
    CHECK(netlist.numEdges() == 20);
    PathFinder pathFinder(netlist);
    // Find path i_value -> o_value
    auto path = pathFinder.find(*netlist.lookupPort("chain_vars.i_value"),
                                *netlist.lookupPort("chain_vars.o_value"));
    CHECK(path.size() == 12);
    CHECK(*path.findVariable("chain_vars.a") == 1);
    CHECK(*path.findVariable("chain_vars.b") == 3);
    CHECK(*path.findVariable("chain_vars.c") == 5);
    CHECK(*path.findVariable("chain_vars.d") == 7);
    CHECK(*path.findVariable("chain_vars.e") == 9);
}

//===---------------------------------------------------------------------===//
// Tests for module instance connectivity.
//===---------------------------------------------------------------------===//

TEST_CASE("Signal passthrough with a nested module") {
    // Test that a nested module is connected correctly.
    auto tree = SyntaxTree::fromText(R"(
module passthrough(input logic i_value, output logic o_value);
  assign o_value = i_value;
endmodule

module nested_passthrough(input logic i_value, output logic o_value);
  passthrough foo(
    .i_value(i_value),
    .o_value(o_value));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    PathFinder pathFinder(netlist);
    auto path = pathFinder.find(*netlist.lookupPort("nested_passthrough.i_value"),
                                *netlist.lookupPort("nested_passthrough.o_value"));
    CHECK(*path.findVariable("nested_passthrough.foo.i_value") == 1);
    CHECK(*path.findVariable("nested_passthrough.foo.o_value") == 2);
}

TEST_CASE("Signal passthrough with a chain of two nested modules") {
    // Test that two nested module are connected correctly.
    auto tree = SyntaxTree::fromText(R"(
module passthrough(input logic i_value, output logic o_value);
  assign o_value = i_value;
endmodule

module nested_passthrough(input logic i_value, output logic o_value);
  logic value;
  passthrough foo_a(
    .i_value(i_value),
    .o_value(value));
  passthrough foo_b(
    .i_value(value),
    .o_value(o_value));
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    PathFinder pathFinder(netlist);
    auto path = pathFinder.find(*netlist.lookupPort("nested_passthrough.i_value"),
                                *netlist.lookupPort("nested_passthrough.o_value"));
    CHECK(path.size() == 8);
    CHECK(*path.findVariable("nested_passthrough.foo_a.i_value") == 1);
    CHECK(*path.findVariable("nested_passthrough.foo_a.o_value") == 2);
    CHECK(*path.findVariable("nested_passthrough.foo_b.i_value") == 5);
    CHECK(*path.findVariable("nested_passthrough.foo_b.o_value") == 6);
}

//===---------------------------------------------------------------------===//
// Tests for variable splitting
//===---------------------------------------------------------------------===//

TEST_CASE("Chain of assignments in a sequence using a vector") {
    // As above but this time using a packed array.
    auto tree = SyntaxTree::fromText(R"(
module chain_array (input logic i_value, output logic o_value);

  logic [4:0] x;

  assign x[0] = i_value;

  always_comb begin
    x[1] = x[0];
    x[2] = x[1];
    x[3] = x[2];
  end

  assign x[4] = x[3];
  assign o_value = x[4];

endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    PathFinder pathFinder(netlist);
    auto path = pathFinder.find(*netlist.lookupPort("chain_array.i_value"),
                                *netlist.lookupPort("chain_array.o_value"));
    CHECK(*path.findVariable("chain_array.x[0]") == 1);
    CHECK(*path.findVariable("chain_array.x[1]") == 3);
    CHECK(*path.findVariable("chain_array.x[2]") == 5);
    CHECK(*path.findVariable("chain_array.x[3]") == 7);
    CHECK(*path.findVariable("chain_array.x[4]") == 9);
}

TEST_CASE("Passthrough two signals via a shared structure") {
    auto tree = SyntaxTree::fromText(R"(
module passthrough_member_access (
  input logic i_value_a,
  input logic i_value_b,
  output logic o_value_a,
  output logic o_value_b
);

  struct packed {
    logic a;
    logic b;
  } foo;

  assign foo.a = i_value_a;
  assign foo.b = i_value_b;

  assign o_value_a = foo.a;
  assign o_value_b = foo.b;

endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    auto* inPortA = netlist.lookupPort("passthrough_member_access.i_value_a");
    auto* inPortB = netlist.lookupPort("passthrough_member_access.i_value_b");
    auto* outPortA = netlist.lookupPort("passthrough_member_access.o_value_a");
    auto* outPortB = netlist.lookupPort("passthrough_member_access.o_value_b");
    PathFinder pathFinder(netlist);
    // Valid paths.
    CHECK(pathFinder.find(*inPortA, *outPortA).size() == 4);
    CHECK(pathFinder.find(*inPortB, *outPortB).size() == 4);
    // Invalid paths.
    CHECK(pathFinder.find(*inPortA, *outPortB).empty());
    CHECK(pathFinder.find(*inPortB, *outPortA).empty());
}

TEST_CASE("Passthrough two signals via ranges in a shared vector") {
    auto tree = SyntaxTree::fromText(R"(
module passthrough_ranges (
  input  logic [1:0] i_value_a,
  input  logic [1:0] i_value_b,
  output logic [1:0] o_value_a,
  output logic [1:0] o_value_b
);

  logic [3:0] foo;

  assign foo[1:0] = i_value_a;
  assign foo[3:2] = i_value_b;

  assign o_value_a = foo[1:0];
  assign o_value_b = foo[3:2];

endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    auto* inPortA = netlist.lookupPort("passthrough_ranges.i_value_a");
    auto* inPortB = netlist.lookupPort("passthrough_ranges.i_value_b");
    auto* outPortA = netlist.lookupPort("passthrough_ranges.o_value_a");
    auto* outPortB = netlist.lookupPort("passthrough_ranges.o_value_b");
    PathFinder pathFinder(netlist);
    // Valid paths.
    CHECK(pathFinder.find(*inPortA, *outPortA).size() == 4);
    CHECK(pathFinder.find(*inPortB, *outPortB).size() == 4);
    // Invalid paths.
    CHECK(pathFinder.find(*inPortA, *outPortB).empty());
    CHECK(pathFinder.find(*inPortB, *outPortA).empty());
}

//===---------------------------------------------------------------------===//
// Tests for loop unrolling
//===---------------------------------------------------------------------===//

TEST_CASE("Chain of assignments using a single loop") {
    // Test that a loop can be unrolled and variable declarations can be split
    // out for elements of an array.
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
    auto netlist = createNetlist(compilation);
    PathFinder pathFinder(netlist);
    // i_value -> o_value, check it passes through each stage.
    CHECK(pathFinder
              .find(*netlist.lookupPort("chain_array.i_value"),
                    *netlist.lookupPort("chain_array.o_value"))
              .size() == 10);
}

TEST_CASE("Chain of assignments using a nested loop") {
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
    auto netlist = createNetlist(compilation);
    PathFinder pathFinder(netlist);
    // i_value -> o_value, check it passes through each stage.
    auto path = pathFinder.find(*netlist.lookupPort("chain_nested.i_value"),
                                *netlist.lookupPort("chain_nested.o_value"));
    CHECK(*path.findVariable("chain_nested.stages[0]") == 1);
    CHECK(*path.findVariable("chain_nested.stages[1]") == 3);
    CHECK(*path.findVariable("chain_nested.stages[2]") == 5);
    CHECK(*path.findVariable("chain_nested.stages[3]") == 7);
    CHECK(*path.findVariable("chain_nested.stages[4]") == 9);
    CHECK(*path.findVariable("chain_nested.stages[5]") == 11);
    CHECK(*path.findVariable("chain_nested.stages[6]") == 13);
    CHECK(*path.findVariable("chain_nested.stages[7]") == 15);
    CHECK(*path.findVariable("chain_nested.stages[8]") == 17);
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
    auto netlist = createNetlist(compilation);
    auto* inPortA = netlist.lookupPort("chain_loop_dual.i_value_a");
    auto* inPortB = netlist.lookupPort("chain_loop_dual.i_value_b");
    auto* outPortA = netlist.lookupPort("chain_loop_dual.o_value_a");
    auto* outPortB = netlist.lookupPort("chain_loop_dual.o_value_b");
    PathFinder pathFinder(netlist);
    // Valid paths.
    CHECK(pathFinder.find(*inPortA, *outPortA).size() == 10);
    CHECK(pathFinder.find(*inPortB, *outPortB).size() == 10);
    // Invalid paths.
    CHECK(pathFinder.find(*inPortA, *outPortB).empty());
    CHECK(pathFinder.find(*inPortB, *outPortA).empty());
}

//===---------------------------------------------------------------------===//
// Tests for conditional variables in procedural blocks.
//===---------------------------------------------------------------------===//

TEST_CASE("Mux") {
    // Test that the variable in a conditional block is correctly added as a
    // dependency on the output variable controlled by that block.
    auto tree = SyntaxTree::fromText(R"(
module mux(input a, input b, input sel, output reg f);
  always @(*) begin
    if (sel == 1'b0) begin
      f = a;
    end else begin
      f = b;
    end
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    PathFinder pathFinder(netlist);
    CHECK(!pathFinder.find(*netlist.lookupPort("mux.sel"), *netlist.lookupPort("mux.f")).empty());
}

TEST_CASE("Nested muxing") {
    // Test that the variables in multiple nested levels of conditions are
    // correctly added as dependencies of the output variable.
    auto tree = SyntaxTree::fromText(R"(
module mux(input a, input b, input c,
           input sel_a, input sel_b,
           output reg f);
  always @(*) begin
    if (sel_a == 1'b0) begin
      if (sel_b == 1'b0)
        f = a;
      else
        f = b;
    end else begin
      f = c;
    end
  end
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    PathFinder pathFinder(netlist);
    CHECK(!pathFinder.find(*netlist.lookupPort("mux.sel_a"), *netlist.lookupPort("mux.f")).empty());
    CHECK(!pathFinder.find(*netlist.lookupPort("mux.sel_b"), *netlist.lookupPort("mux.f")).empty());
}

//===---------------------------------------------------------------------===//
// Tests for name resolution
//===---------------------------------------------------------------------===//

TEST_CASE("Unused modules") {
    // Test that unused modules are not visited by the netlist builder.
    // See Issue #793.
    auto tree = SyntaxTree::fromText(R"(
module test (input i1,
             input i2,
             output o1
             );
   cell_a i_cell_a(.d1(i1),
                   .d2(i2),
                   .c(o1));
endmodule

module cell_a(input  d1,
              input  d2,
              output c);
   assign c = d1 + d2;
endmodule

// unused
module cell_b(input  a,
              input  b,
              output z);
   assign z = a || b;
endmodule

// unused
module cell_c(input  a,
              input  b,
              output z);
   assign z = (!a) && b;
endmodule
)");
    CompilationOptions coptions;
    coptions.topModules.emplace("test"sv);
    Bag options;
    options.set(coptions);
    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(netlist.numNodes() > 0);
}
