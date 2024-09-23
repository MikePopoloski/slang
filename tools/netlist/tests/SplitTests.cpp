//------------------------------------------------------------------------------
//! @file NetlistTest.cpp
//! @brief Variable splitting unit tests.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "NetlistTest.h"
#include "Test.h"

// Test the logic that splits variable declaration nodes into sets of ALIAS
// nodes with connections based on their selection bounds.

TEST_CASE("One in, two out") {
    auto tree = SyntaxTree::fromText(R"(
module foo(
  input logic [15:0] a,
  output logic [7:0] b,
  output logic [7:0] c
);

  logic [15:0] x;

  assign x = a;
  assign b = x[7:0];
  assign c = x[15:8];

endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    // foo.x should have one ALIAS.
    auto v = netlist.lookupVariable("foo.x");
    CHECK(v != nullptr);
    CHECK(v->aliases.size() == 1);
}

TEST_CASE("Two in, one out") {
    auto tree = SyntaxTree::fromText(R"(
module foo(
  input logic [7:0] a,
  input logic [7:0] b,
  output logic [15:0] c
);

  logic [15:0] x;

  assign x[7:0] = a;
  assign x[15:8] = b;
  assign c = x;

endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    // foo.x should have two ALIAS components.
    auto v = netlist.lookupVariable("foo.x");
    CHECK(v != nullptr);
    CHECK(v->aliases.size() == 0);
}

TEST_CASE("Two in, two out") {
    auto tree = SyntaxTree::fromText(R"(
module foo(
  input logic [7:0] a,
  input logic [7:0] b,
  output logic [7:0] c,
  output logic [7:0] d
);

  logic [15:0] x;

  assign x[7:0] = a;
  assign x[15:8] = b;
  assign c = x[7:0];
  assign d = x[15:8];

endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    // foo.x should have two ALIAS components.
    auto v = netlist.lookupVariable("foo.x");
    CHECK(v != nullptr);
    CHECK(v->aliases.size() == 2);
}
