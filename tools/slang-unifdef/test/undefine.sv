// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s -U FEATURE_TOGGLE
// CHECK-STDOUT: %b.out.sv

module top;
`ifdef FEATURE_TOGGLE
  logic enabled_branch;
`else
  logic disabled_branch;
`endif

`ifndef FEATURE_TOGGLE
  logic undef_guard;
`endif
endmodule
