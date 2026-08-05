// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// An unknown `elsif after a forced-true branch is unreachable, so it is dropped.

// RUN: %unifdef %s --define MACRO_A
// CHECK-STDOUT: %b.out.sv

module top;
`ifdef MACRO_A
  logic branch_a;
`elsif MACRO_B
  logic branch_b;
`endif
endmodule
