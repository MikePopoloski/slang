//------------------------------------------------------------------------------
//! @file CombLoopsTests.cpp
//! @brief CombLooops unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "CombLoops.h"
#include "NetlistTest.h"
#include "Test.h"

//===---------------------------------------------------------------------===//
// Basic tests
//===---------------------------------------------------------------------===//

TEST_CASE("A simple combinatorial loop") {
    auto tree = SyntaxTree::fromText(R"(
module test;
wire a;
wire b;

t2 t2(
  .x(a),
  .y(b)
);
assign a = b;
endmodule

module t2(input x, output y);
assign y = x;
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    ElementaryCyclesSearch ecs(netlist);
    std::vector<CycleListType>* cycles_ptr = ecs.getElementaryCycles();
    std::vector<CycleListType>& cycles = *cycles_ptr;
    CHECK(cycles.size() == 1);
    CHECK(cycles[0].size() == 10);
    CHECK(count_vec_if(cycles[0], [&netlist](int node) {
              return (netlist.getNode(node).kind == NodeKind::VariableReference);
          }) == 6);
}

TEST_CASE("A combinatorial loop with a single posedge DFF path") {
    // Test that a DFF in a closed path prevents
    // the loop from being counted as combinatorial
    auto tree = SyntaxTree::fromText(R"(
module test (input clk);
wire a;
wire b;
wire c;
wire d;

t2 t2(
  .clk(clk),
  .x(a),
  .y(b),
  .z(c)
);
assign a = b & c;
endmodule

module t2(input clk, input x, output y, output reg z);
assign y = x;
always @(posedge clk)
  z <= x;
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    ElementaryCyclesSearch ecs(netlist);
    std::vector<CycleListType>* cycles_ptr = ecs.getElementaryCycles();
    std::vector<CycleListType>& cycles = *cycles_ptr;
    CHECK(cycles.size() == 1);
    CHECK(cycles[0].size() == 10);
    CHECK(count_vec_if(cycles[0], [&netlist](int node) {
              return (netlist.getNode(node).kind == NodeKind::VariableReference);
          }) == 6);
}

TEST_CASE("A combinatorial loop with multiple edges DFF path") {
    // Test that a DFF in a closed path prevents
    // the loop from being counted as combinatorial
    auto tree = SyntaxTree::fromText(R"(
module test (input clk, input rst);
wire a;
wire b;
wire c;
wire d;

t2 t2(
  .clk(clk),
  .rst(rst),
  .x(a),
  .y(b),
  .z(c)
);
assign a = b & c;
endmodule

module t2(input clk, input rst, input x, output y, output reg z);
assign y = x;
always @(posedge clk or negedge rst)
  if (!rst)
    z <= 1'b0;
  else
    z <= x;
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    ElementaryCyclesSearch ecs(netlist);
    std::vector<CycleListType>* cycles_ptr = ecs.getElementaryCycles();
    std::vector<CycleListType>& cycles = *cycles_ptr;
    CHECK(cycles.size() == 1);
    CHECK(cycles[0].size() == 10);
    CHECK(count_vec_if(cycles[0], [&netlist](int node) {
              return (netlist.getNode(node).kind == NodeKind::VariableReference);
          }) == 6);
}

TEST_CASE("A combinatorial loop with a combinatorial event list") {
    // Test that a csensitivity list with a nonedge signal in the
    // sensitivity list is detected as a ccombinatorial loop
    auto tree = SyntaxTree::fromText(R"(
module test (input clk, input rst);
wire a;
wire b;
wire c;
wire d;

t2 t2(
  .clk(clk),
  .rst(rst),
  .x(a),
  .y(b),
  .z(c)
);
assign a = b & c;
endmodule

module t2(input clk, input rst, input x, output y, output reg z);
assign y = x;
always @(posedge clk or x)
    z <= x;
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    ElementaryCyclesSearch ecs(netlist);
    std::vector<CycleListType>* cycles_ptr = ecs.getElementaryCycles();
    std::vector<CycleListType>& cycles = *cycles_ptr;
    CHECK(cycles.size() == 2);
    CHECK(cycles[0].size() == 10);
    CHECK(count_vec_if(cycles[0], [&netlist](int node) {
              return (netlist.getNode(node).kind == NodeKind::VariableReference);
          }) == 6);
}
