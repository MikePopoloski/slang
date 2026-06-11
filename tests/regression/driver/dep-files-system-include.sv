// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// A `include <foo>` system-style include that resolves through --isystem is a
// real build dependency and should appear in the depfile, just like a `include
// "foo"`.

// RUN: %slang %s --isystem %data --Mall - 2>&1
// CHECK: file_defn.svh
// CHECK-NEXT: dep-files-system-include.sv

`include <file_defn.svh>

module m;
    string s = `FOO;
endmodule
