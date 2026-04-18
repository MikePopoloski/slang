// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %s -Wwidth-trunc --suppress-macro-warnings %data/nested/ -I %data 2>&1
// CHECK: Build succeeded: 0 errors, 0 warnings

`include "nested/macro.svh"

module m;
    logic [3:0] a;
    `FOO(a);
endmodule
