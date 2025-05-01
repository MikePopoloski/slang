//------------------------------------------------------------------------------
//! @file VariableSelectorsTests.cpp
//! @brief Tests for handling of variable selectors.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "NetlistTest.h"
#include "Test.h"

//===---------------------------------------------------------------------===//
// Tests for name resolution.
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

TEST_CASE("Ignore concurrent assertions") {
    // Test that we are not confused by timing events inside concurrent assertions
    auto tree = SyntaxTree::fromText(R"(
module t33 #(
  parameter MODE = 3'd0
) (
  input wire  clk,
  input wire [15:0]l,
  input wire [15:0]s,
  input wire [15:0]c,
  input wire  [1:0]b,
  input wire       a
);
  reg   [15:0] c_n;
  always @(s or l or c)
  begin : c_inc
    c_n = c + (l ^ s);
  end

  property test_prop;
    @(posedge clk) disable iff (MODE != 3'd0)
    (!$isunknown({a,b,c})) &
      a & (b == 2'b01)
      |-> (c_n[15:12] == c[15:12]);
  endproperty
  tp_inst: assert property (test_prop) else
        $error("prop error");
endmodule
)");
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
    auto netlist = createNetlist(compilation);
    CHECK(netlist.numNodes() > 0);
}
