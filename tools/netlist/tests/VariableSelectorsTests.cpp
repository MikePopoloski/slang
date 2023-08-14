//------------------------------------------------------------------------------
//! @file VariableSelectorsTests.cpp
//! @brief Tests for handling of variable selectors.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "NetlistTest.h"


TEST_CASE("Scalar element") {
    // Test element select on a scalar variable.
    auto tree = SyntaxTree::fromText(R"(
module m (input logic i_a,
          input logic i_b,
          output logic o_a,
          output logic o_b);
  int foo;
  assign foo[1] = i_a;
  assign foo[0] = i_b;
  assign o_a = foo[1];
  assign o_b = foo[0];
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(pathExists(netlist, "m.i_a", "m.o_a"));
    CHECK(pathExists(netlist, "m.i_b", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_a", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_b", "m.o_a"));
}

TEST_CASE("Scalar range") {
    // Test range select on a scalar variable.
    auto tree = SyntaxTree::fromText(R"(
module m (input logic [1:0] i_a,
          input logic [1:0] i_b,
          output logic [1:0] o_a,
          output logic [1:0] o_b);
  int foo;
  assign foo[3:2] = i_a;
  assign foo[1:0] = i_b;
  assign o_a = foo[3:2];
  assign o_b = foo[1:0];
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    PathFinder pathFinder(netlist);
    CHECK(pathExists(netlist, "m.i_a", "m.o_a"));
    CHECK(pathExists(netlist, "m.i_b", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_a", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_b", "m.o_a"));
}

TEST_CASE("Scalar range 2") {
    // Test stacked range selects on a scalar variable.
    auto tree = SyntaxTree::fromText(R"(
module m (input logic [3:0] i_a,
          input logic [3:0] i_b,
          output logic [1:0] o_a,
          output logic [1:0] o_b);
  int foo;
  assign foo[7:4] = i_a;
  assign foo[3:0] = i_b;
  assign o_a = foo[7:4][6:5];
  assign o_b = foo[3:0][2:1];
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    PathFinder pathFinder(netlist);
    CHECK(pathExists(netlist, "m.i_a", "m.o_a"));
    CHECK(pathExists(netlist, "m.i_b", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_a", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_b", "m.o_a"));
}

TEST_CASE("Packed array element") {
    // Test element select on a packed array variable.
    auto tree = SyntaxTree::fromText(R"(
module m (input logic i_a,
          input logic i_b,
          output logic o_a,
          output logic o_b);
  logic [1:0] foo;
  assign foo[1] = i_a;
  assign foo[0] = i_b;
  assign o_a = foo[1];
  assign o_b = foo[0];
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(pathExists(netlist, "m.i_a", "m.o_a"));
    CHECK(pathExists(netlist, "m.i_b", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_a", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_b", "m.o_a"));
}

TEST_CASE("Unpacked array element") {
    // Test element select on an unpacked array variable.
    auto tree = SyntaxTree::fromText(R"(
module m (input logic i_a,
          input logic i_b,
          output logic o_a,
          output logic o_b);
  logic foo [1:0];
  assign foo[1] = i_a;
  assign foo[0] = i_b;
  assign o_a = foo[1];
  assign o_b = foo[0];
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(pathExists(netlist, "m.i_a", "m.o_a"));
    CHECK(pathExists(netlist, "m.i_b", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_a", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_b", "m.o_a"));
}


TEST_CASE("Packed array range") {
    // Test range select on a packed array variable.
    auto tree = SyntaxTree::fromText(R"(
module m (input logic [1:0] i_a,
          input logic [1:0] i_b,
          output logic [1:0] o_a,
          output logic [1:0] o_b);
  logic [3:0] foo;
  assign foo[3:2] = i_a;
  assign foo[1:0] = i_b;
  assign o_a = foo[3:2];
  assign o_b = foo[1:0];
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    PathFinder pathFinder(netlist);
    CHECK(pathExists(netlist, "m.i_a", "m.o_a"));
    CHECK(pathExists(netlist, "m.i_b", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_a", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_b", "m.o_a"));
}

TEST_CASE("Packed array range 2") {
    // Test stacked range selects on a packed array variable.
    auto tree = SyntaxTree::fromText(R"(
module m (input logic [3:0] i_a,
          input logic [3:0] i_b,
          output logic [1:0] o_a,
          output logic [1:0] o_b);
  logic [7:0] foo;
  assign foo[7:4] = i_a;
  assign foo[3:0] = i_b;
  assign o_a = foo[7:4][6:5];
  assign o_b = foo[3:0][2:1];
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    PathFinder pathFinder(netlist);
    CHECK(pathExists(netlist, "m.i_a", "m.o_a"));
    CHECK(pathExists(netlist, "m.i_b", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_a", "m.o_b"));
    CHECK(!pathExists(netlist, "m.i_b", "m.o_a"));
}



//===---------------------------------------------------------------------===//
// Tests for variable splitting
//===---------------------------------------------------------------------===//

//TEST_CASE("Chain of assignments in a sequence using a vector") {
//    // As above but this time using a packed array.
//    auto tree = SyntaxTree::fromText(R"(
//module chain_array (input logic i_value, output logic o_value);
//
//  logic [4:0] x;
//
//  assign x[0] = i_value;
//
//  always_comb begin
//    x[1] = x[0];
//    x[2] = x[1];
//    x[3] = x[2];
//  end
//
//  assign x[4] = x[3];
//  assign o_value = x[4];
//
//endmodule
//)");
//    Compilation compilation;
//    compilation.addSyntaxTree(tree);
//    NO_COMPILATION_ERRORS;
//    auto netlist = createNetlist(compilation);
//    PathFinder pathFinder(netlist);
//    auto path = pathFinder.find(*netlist.lookupPort("chain_array.i_value"),
//                                *netlist.lookupPort("chain_array.o_value"));
//    CHECK(*path.findVariable("chain_array.x[0]") == 1);
//    CHECK(*path.findVariable("chain_array.x[1]") == 3);
//    CHECK(*path.findVariable("chain_array.x[2]") == 5);
//    CHECK(*path.findVariable("chain_array.x[3]") == 7);
//    CHECK(*path.findVariable("chain_array.x[4]") == 9);
//}
//
//TEST_CASE("Passthrough two signals via a shared structure") {
//    auto tree = SyntaxTree::fromText(R"(
//module passthrough_member_access (
//  input logic i_value_a,
//  input logic i_value_b,
//  output logic o_value_a,
//  output logic o_value_b
//);
//
//  struct packed {
//    logic a;
//    logic b;
//  } foo;
//
//  assign foo.a = i_value_a;
//  assign foo.b = i_value_b;
//
//  assign o_value_a = foo.a;
//  assign o_value_b = foo.b;
//
//endmodule
//)");
//    Compilation compilation;
//    compilation.addSyntaxTree(tree);
//    NO_COMPILATION_ERRORS;
//    auto netlist = createNetlist(compilation);
//    auto* inPortA = netlist.lookupPort("passthrough_member_access.i_value_a");
//    auto* inPortB = netlist.lookupPort("passthrough_member_access.i_value_b");
//    auto* outPortA = netlist.lookupPort("passthrough_member_access.o_value_a");
//    auto* outPortB = netlist.lookupPort("passthrough_member_access.o_value_b");
//    PathFinder pathFinder(netlist);
//    // Valid paths.
//    CHECK(pathFinder.find(*inPortA, *outPortA).size() == 4);
//    CHECK(pathFinder.find(*inPortB, *outPortB).size() == 4);
//    // Invalid paths.
//    CHECK(pathFinder.find(*inPortA, *outPortB).empty());
//    CHECK(pathFinder.find(*inPortB, *outPortA).empty());
//}
//
//TEST_CASE("Passthrough two signals via ranges in a shared vector") {
//    auto tree = SyntaxTree::fromText(R"(
//module passthrough_ranges (
//  input  logic [1:0] i_value_a,
//  input  logic [1:0] i_value_b,
//  output logic [1:0] o_value_a,
//  output logic [1:0] o_value_b
//);
//
//  logic [3:0] foo;
//
//  assign foo[1:0] = i_value_a;
//  assign foo[3:2] = i_value_b;
//
//  assign o_value_a = foo[1:0];
//  assign o_value_b = foo[3:2];
//
//endmodule
//)");
//    Compilation compilation;
//    compilation.addSyntaxTree(tree);
//    NO_COMPILATION_ERRORS;
//    auto netlist = createNetlist(compilation);
//    auto* inPortA = netlist.lookupPort("passthrough_ranges.i_value_a");
//    auto* inPortB = netlist.lookupPort("passthrough_ranges.i_value_b");
//    auto* outPortA = netlist.lookupPort("passthrough_ranges.o_value_a");
//    auto* outPortB = netlist.lookupPort("passthrough_ranges.o_value_b");
//    PathFinder pathFinder(netlist);
//    // Valid paths.
//    CHECK(pathFinder.find(*inPortA, *outPortA).size() == 4);
//    CHECK(pathFinder.find(*inPortB, *outPortB).size() == 4);
//    // Invalid paths.
//    CHECK(pathFinder.find(*inPortA, *outPortB).empty());
//    CHECK(pathFinder.find(*inPortB, *outPortA).empty());
//}

//===---------------------------------------------------------------------===//
// Tests for loop unrolling
//===---------------------------------------------------------------------===//

//TEST_CASE("Chain of assignments using a single loop") {
//    // Test that a loop can be unrolled and variable declarations can be split
//    // out for elements of an array.
//    auto tree = SyntaxTree::fromText(R"(
//module chain_array #(parameter N=4) (
//  input logic i_value,
//  output logic o_value);
//
//  logic pipeline [N-1:0];
//
//  assign pipeline[0] = i_value;
//
//  always_comb begin
//    for (int i=1; i<N; i++) begin
//      pipeline[i] = pipeline[i-1];
//    end
//  end
//
//  assign o_value = pipeline[N-1];
//
//endmodule
//)");
//    Compilation compilation;
//    compilation.addSyntaxTree(tree);
//    NO_COMPILATION_ERRORS;
//    auto netlist = createNetlist(compilation);
//    PathFinder pathFinder(netlist);
//    // i_value -> o_value, check it passes through each stage.
//    CHECK(pathFinder
//              .find(*netlist.lookupPort("chain_array.i_value"),
//                    *netlist.lookupPort("chain_array.o_value"))
//              .size() == 10);
//}
//
//TEST_CASE("Chain of assignments using a nested loop") {
//    // Expand the previous test to check the handling of multiple loop variables.
//    auto tree = SyntaxTree::fromText(R"(
//module chain_nested #(parameter N=3) (
//  input logic i_value,
//  output logic o_value);
//
//  logic [(N*N)-1:0] stages;
//
//  //assign stages[0] = i_value;
//  assign o_value = stages[(N*N)-1];
//
//  always_comb begin
//    for (int i=0; i<N; i++) begin
//      for (int j=0; j<N; j++) begin
//        if ((i == 0) && (j == 0))
//          stages[0] = i_value;
//        else
//          stages[(i*N + j)] = stages[(i*N + j)-1];
//      end
//    end
//  end
//
//endmodule
//)");
//    Compilation compilation;
//    compilation.addSyntaxTree(tree);
//    NO_COMPILATION_ERRORS;
//    auto netlist = createNetlist(compilation);
//    PathFinder pathFinder(netlist);
//    // i_value -> o_value, check it passes through each stage.
//    auto path = pathFinder.find(*netlist.lookupPort("chain_nested.i_value"),
//                                *netlist.lookupPort("chain_nested.o_value"));
//    CHECK(*path.findVariable("chain_nested.stages[0]") == 1);
//    CHECK(*path.findVariable("chain_nested.stages[1]") == 3);
//    CHECK(*path.findVariable("chain_nested.stages[2]") == 5);
//    CHECK(*path.findVariable("chain_nested.stages[3]") == 7);
//    CHECK(*path.findVariable("chain_nested.stages[4]") == 9);
//    CHECK(*path.findVariable("chain_nested.stages[5]") == 11);
//    CHECK(*path.findVariable("chain_nested.stages[6]") == 13);
//    CHECK(*path.findVariable("chain_nested.stages[7]") == 15);
//    CHECK(*path.findVariable("chain_nested.stages[8]") == 17);
//}
//
//TEST_CASE("Two chains of assignments using a shared 2D array") {
//    // Check that assignments corresponding to two distinct paths, using the same
//    // array variable can be handled.
//    auto tree = SyntaxTree::fromText(R"(
//module chain_loop_dual #(parameter N=4)(
//  input logic i_value_a,
//  input logic i_value_b,
//  output logic o_value_a,
//  output logic o_value_b
//);
//
//  parameter A = 0;
//  parameter B = 1;
//
//  logic pipeline [1:0][N-1:0];
//
//  assign pipeline[A][0] = i_value_a;
//  assign pipeline[B][0] = i_value_b;
//
//  always_comb begin
//    for (int i=1; i<N; i++) begin
//      pipeline[A][i] = pipeline[A][i-1];
//      pipeline[B][i] = pipeline[B][i-1];
//    end
//  end
//
//  assign o_value_a = pipeline[A][N-1];
//  assign o_value_b = pipeline[B][N-1];
//
//endmodule
//)");
//    Compilation compilation;
//    compilation.addSyntaxTree(tree);
//    NO_COMPILATION_ERRORS;
//    auto netlist = createNetlist(compilation);
//    auto* inPortA = netlist.lookupPort("chain_loop_dual.i_value_a");
//    auto* inPortB = netlist.lookupPort("chain_loop_dual.i_value_b");
//    auto* outPortA = netlist.lookupPort("chain_loop_dual.o_value_a");
//    auto* outPortB = netlist.lookupPort("chain_loop_dual.o_value_b");
//    PathFinder pathFinder(netlist);
//    // Valid paths.
//    CHECK(pathFinder.find(*inPortA, *outPortA).size() == 10);
//    CHECK(pathFinder.find(*inPortB, *outPortB).size() == 10);
//    // Invalid paths.
//    CHECK(pathFinder.find(*inPortA, *outPortB).empty());
//    CHECK(pathFinder.find(*inPortB, *outPortA).empty());
//}
