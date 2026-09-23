// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %unifdef %s -U FEATURE_TOGGLE
// CHECK-STDOUT: %b.out.sv

module top;
  logic disabled_branch;

  logic undef_guard;
endmodule
