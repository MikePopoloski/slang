// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s -UMACRO_A -DMACRO_B
// CHECK-STDOUT: %b.out.sv

module top;
  logic branch_b;
endmodule
