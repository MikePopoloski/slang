// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s --define ENABLE_FEATURE
// CHECK-STDOUT: %b.out.sv

// Because ENABLE_FEATURE is defined, the whole `ifndef region is removed, including
// nested conditionals and the matching `endif, while `keep_me survives.

// A false `ifndef with no `else is removed entirely.

// A live nested `ifdef inside a surviving `else branch keeps its own scaffolding.

module top;
`ifndef ENABLE_FEATURE
  logic internal_a;
`ifdef OTHER
  logic nested_in_internal;
`endif
`endif
  logic keep_me;
`ifndef ENABLE_FEATURE
  logic bare_internal;
`endif
`ifndef ENABLE_FEATURE
  logic internal_only;
`else
  logic public_a;
`ifdef FEATURE_X
  logic feature;
`endif
  logic public_b;
`endif
  logic tail;
endmodule
