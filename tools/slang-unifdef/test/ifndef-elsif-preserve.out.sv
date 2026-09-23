// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// An unknown `elsif after a forced-false starting branch remains as a residual `ifdef.

// RUN: %unifdef %s -D MACRO_A
// CHECK-STDOUT: %b.out.sv

module top;
`ifdef MACRO_B
  logic branch_b;
`endif
endmodule
