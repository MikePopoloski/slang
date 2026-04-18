// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// show-parsed-files lists every source and include file that was parsed.
// RUN: %slang %s %data/test6.sv --single-unit --show-parsed-files -I %data 2>&1
// CHECK: show-parsed-files.sv
// CHECK: test6.sv
// CHECK: macro.svh

module k;
    logic [3:0] a;
    logic [2:0] b = a;
endmodule
