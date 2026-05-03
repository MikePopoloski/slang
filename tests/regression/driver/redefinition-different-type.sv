// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// Redeclaration with a different type is an error in strict mode.
// RUN: %slang %s 2>&1 || true
// CHECK: error:
// CHECK: Build failed

// Some tools issue only a warning; --compat=all keeps it as a warning.
// RUN: %slang %s --compat=all 2>&1
// CHECK: -Wredefinition-different-type]
// CHECK: Build succeeded

module m;
  int i;
  bit [3:0] i;
endmodule
