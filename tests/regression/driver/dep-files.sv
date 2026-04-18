// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %s -I %data --Minclude - 2>&1
// CHECK: file_defn.svh

// RUN: %slang %s -I %data --Minclude - --depfile-target target 2>&1
// CHECK: target:{{.*}}file_defn.svh

// RUN: %slang %s -I %data --Mmodule - 2>&1
// CHECK: dep-files.sv

// RUN: %slang %s -I %data --Mmodule - --depfile-target target 2>&1
// CHECK: target:{{.*}}dep-files.sv

// RUN: %slang %s -I %data --Mall - 2>&1
// CHECK: file_defn.svh
// CHECK-NEXT: {{.*}}dep-files.sv

// RUN: %slang %s -I %data --Mall - --depfile-target target 2>&1
// CHECK: target:{{.*}}file_defn.svh{{.*}}dep-files.sv

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
