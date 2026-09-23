// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s -U MACRO_A,MACRO_B,MACRO_D -D MACRO_C
// CHECK-STDOUT: %b.out.sv

module top;
  logic branch_c;
endmodule
