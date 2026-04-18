// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// Test 1: default behavior raises an error for duplicate package
// RUN: %slang %s 2>&1 || true
// CHECK: duplicate definition of 'dup_pkg'
// CHECK: Build failed: 1 error, 0 warnings

// Test 2: -Wno-error=duplicate-definition downgrades the error to a warning
// RUN: %slang %s -Wno-error=duplicate-definition 2>&1
// CHECK: duplicate definition of 'dup_pkg'
// CHECK: Build succeeded: 0 errors, 1 warning

package dup_pkg;
endpackage

package dup_pkg;
endpackage

module top;
endmodule
