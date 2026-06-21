// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// Simple smoke test for memory stats dumping.

// RUN: %slang %s --memory-stats -
// CHECK: Build succeeded
// CHECK: Memory Usage Report
// CHECK: ModuleHeader
// CHECK: CompilationUnit

module m;
endmodule
