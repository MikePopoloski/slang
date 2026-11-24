// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// An assignment in a module-level variable initializer is an error by default.
// RUN: %slang %s 2>&1 || true
// CHECK: error: assignment expressions are not allowed outside of procedural code
// CHECK: Build failed

// The error can be downgraded to a warning.
// RUN: %slang %s -Wno-error=nonprocedural-assign 2>&1
// CHECK: warning: assignment expressions are not allowed outside of procedural code
// CHECK: Build succeeded: 0 errors, 1 warning

// It remains an error in VCS compatibility mode.
// RUN: %slang %s --compat vcs 2>&1 || true
// CHECK: error: assignment expressions are not allowed outside of procedural code
// CHECK: Build failed

module top;
  int a;
  int x = (a = 1);
endmodule
