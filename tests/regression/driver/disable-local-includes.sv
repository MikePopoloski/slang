// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// --disable-local-includes prevents the include from being found via the local directory.
// RUN: %slang %s --disable-local-includes 2>&1 || true
// CHECK: file_defn.svh

`include "file_defn.svh"
`define ID(x) x

module m;
    // hello
    int i = 32'haa_bb??e;
    string s = `FOO;

    begin end
endmodule

`ifdef FOOBAR
`include "mod1.sv"
`endif
