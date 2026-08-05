// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s --define MACRO_B --undefine MACRO_C
// CHECK-STDOUT: %b.out.sv

module top;
`ifdef MACRO_A
  logic branch_a;
`else
  logic branch_b;
`endif
endmodule
