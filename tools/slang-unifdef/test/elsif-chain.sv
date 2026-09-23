// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s -UMACRO_A -DMACRO_B
// CHECK-STDOUT: %b.out.sv

module top;
`ifdef MACRO_A
  logic branch_a;
`elsif MACRO_B
  logic branch_b;
`else
  logic fallback_impl;
`endif
endmodule
