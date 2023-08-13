//------------------------------------------------------------------------------
//! @file NetlistTest.cpp
//! @brief Netlist unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "NetlistTest.h"

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
