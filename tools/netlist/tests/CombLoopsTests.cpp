//------------------------------------------------------------------------------
//! @file CombLoopsTests.cpp
//! @brief CombLooops unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "CombLoops.h"
#include "NetlistTest.h"

//===---------------------------------------------------------------------===//
// Basic tests
//===---------------------------------------------------------------------===//

TEST_CASE("A simple combinatorial loop") {
    // Test that correct dependencies can be formed from procedural and
    // continuous assignments.
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
    CHECK(std::count_if(cycles[0].begin(), cycles[0].end(), [&netlist](int node) {
              return (netlist.getNode(node).kind == NodeKind::VariableReference);
          }) == 6);
}
