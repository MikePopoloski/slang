// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s -U MACRO_A,MACRO_B,MACRO_D -D MACRO_C
// CHECK-STDOUT: %b.out.sv

module top;
`ifdef MACRO_A
  logic branch_a;
`elsif MACRO_B
  logic branch_b;
`elsif MACRO_C
  logic branch_c;
`elsif MACRO_D
  logic branch_d;
`else
  logic fallback_impl;
`endif
endmodule
