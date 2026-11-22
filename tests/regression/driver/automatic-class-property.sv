// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The automatic keyword on a class property is an error by default.
// RUN: %slang %s 2>&1 || true
// CHECK: error: class properties cannot be declared 'automatic'
// CHECK: Build failed

// The error can be downgraded to a warning.
// RUN: %slang %s -Wno-error=automatic-class-property 2>&1
// CHECK: warning: class properties cannot be declared 'automatic'
// CHECK: Build succeeded: 0 errors, 1 warning

// VCS compatibility mode turns it off.
// RUN: %slang %s --compat vcs 2>&1
// CHECK: Build succeeded: 0 errors, 0 warnings

class C;
  automatic int h;
endclass

module top;
  C c;
endmodule
