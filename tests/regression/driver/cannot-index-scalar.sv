// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The LRM does not define bit-select on a scalar type; strict mode is an error.
// RUN: %slang %s 2>&1 || true
// CHECK: error:
// CHECK: Build failed

// Some tools issue only a warning; --compat=all keeps it as a warning.
// RUN: %slang %s --compat=all 2>&1
// CHECK: -Wcannot-index-scalar]
// CHECK: Build succeeded

module scalar_bit_indexed;
  bit flag;
  int i;
  initial begin
    i = 0;
    if (flag[i]) $display("set");
  end
endmodule
