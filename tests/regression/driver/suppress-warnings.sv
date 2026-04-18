// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// -Weverything triggers width-trunc; --suppress-warnings covers the test directory
// so warnings from this file are suppressed.
// RUN: %slang %s -Weverything --suppress-warnings %testdir 2>&1
// CHECK: Build succeeded: 0 errors, 0 warnings

module k;
    logic [3:0] a;
    logic [2:0] b = a;
endmodule
