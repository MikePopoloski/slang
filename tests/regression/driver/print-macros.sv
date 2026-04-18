// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang -E --preprocess-source %s -DFOOBAR -I %data -I %data/libtest 2>&1
// CHECK: // {{.*}}.sv:{{[0-9]+}}
// CHECK-NEXT: module m;
// CHECK: // {{.*}}mod1.sv:1
// CHECK-NEXT: module mod1

// RUN: %slang --macros-only %s -I %data 2>&1
// CHECK: BAR `__FILE__
// CHECK: FOO `BAR
// CHECK: ID(x) x
// CHECK: __slang__ 1
// CHECK: __slang_major__
// CHECK: __slang_minor__

// RUN: %slang --macros-only --group-macros-by-file %s -I %data 2>&1
// CHECK: print-macros.sv:
// CHECK-NEXT: ID(x) x

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
