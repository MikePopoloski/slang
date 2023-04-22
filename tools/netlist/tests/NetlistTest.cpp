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
}


