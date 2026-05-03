// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// A named parameter override that refers to a non-existent parameter is an
// error in strict mode.
// RUN: %slang %s 2>&1 || true
// CHECK: error:
// CHECK: Build failed

// Some tools issue only a warning and silently ignore the override;
// --compat=all keeps it as a warning.
// RUN: %slang %s --compat=all 2>&1
// CHECK: -Wundefined-param-override]
// CHECK: Build succeeded

module bot(input clk);
  parameter TYPE = 0;
endmodule

module top;
  logic clk;
  bot #(.TYPE(1), .WIDTH(1)) b(clk);
endmodule
