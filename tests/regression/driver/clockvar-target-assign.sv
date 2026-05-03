// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The LRM prohibits continuous assignments to output clockvars; strict mode is an error.
// RUN: %slang %s 2>&1 || true
// CHECK: error:
// CHECK: Build failed

// Some tools accept it; --compat=all downgrades to a warning.
// RUN: %slang %s --compat=all 2>&1
// CHECK: -Wclockvar-target-assign]
// CHECK: Build succeeded: 0 errors, 1 warning

module m(input clk);
    int j;
    assign j = 1;
    clocking cb @(posedge clk);
        output j;
    endclocking
endmodule
