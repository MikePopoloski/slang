// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %s --compat=all 2>&1
// CHECK: Build succeeded: 0 errors, 1 warning

module m;
    int i = $foo;
endmodule
