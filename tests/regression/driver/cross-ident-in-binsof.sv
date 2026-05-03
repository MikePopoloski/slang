// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// The LRM disallows cross_identifier as a bins_expression; strict mode is an error.
// RUN: %slang %s 2>&1 || true
// CHECK: error:
// CHECK: Build failed

// Some tools accept this; --compat=all keeps the diagnostic as a warning.
// RUN: %slang %s --compat=all 2>&1
// CHECK: -Wcross-ident-in-binsof]
// CHECK: Build succeeded

module m;
    logic clk, a, b, c;
    covergroup cg @(posedge clk);
        cp_a : coverpoint a { bins zero = {0}; bins one = {1}; }
        cp_b : coverpoint b { bins zero = {0}; bins one = {1}; }
        cp_c : coverpoint c { bins zero = {0}; bins one = {1}; }
        cp_a_cross_b : cross cp_a, cp_b {
            bins both_one = binsof(cp_a.one) && binsof(cp_b.one);
        }
        cp_nested : cross cp_a_cross_b, cp_c {
            bins with_c = binsof(cp_a_cross_b) && binsof(cp_c.one);
        }
    endgroup
    cg cg_inst = new();
endmodule
