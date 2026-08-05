// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s --define MACRO_B --undefine MACRO_C
// CHECK-STDOUT: %b.out.sv

module top;
`ifdef MACRO_A
  logic branch_a;
`elsif MACRO_B
  logic branch_b;
`elsif MACRO_C
  logic branch_c;
`else
  logic fallback_impl;
`endif
endmodule
