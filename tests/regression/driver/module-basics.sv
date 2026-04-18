// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %s -I %data 2>&1
// CHECK: Build succeeded

// RUN: %slang %s -I %data -Tmin --max-include-depth=4 --max-parse-depth=10 --max-lexer-errors=2 --max-hierarchy-depth=10 --max-generate-steps=1 --max-constexpr-depth=1 --max-constexpr-steps=2 --constexpr-backtrace-limit=4 --max-instance-array=5 --max-enum-values=100 --ignore-unknown-modules --relax-enum-conversions --allow-hierarchical-const --allow-dup-initial-drivers --lint-only --color-diagnostics=false --timescale=10ns/10ps 2>&1
// RUN: %slang %s -I %data -Ttyp --max-include-depth=4 --max-parse-depth=10 --max-lexer-errors=2 --max-hierarchy-depth=10 --max-generate-steps=1 --max-constexpr-depth=1 --max-constexpr-steps=2 --constexpr-backtrace-limit=4 --max-instance-array=5 --max-enum-values=100 --ignore-unknown-modules --relax-enum-conversions --allow-hierarchical-const --allow-dup-initial-drivers --lint-only --color-diagnostics=false --timescale=10ns/10ps 2>&1
// RUN: %slang %s -I %data -Tmax --max-include-depth=4 --max-parse-depth=10 --max-lexer-errors=2 --max-hierarchy-depth=10 --max-generate-steps=1 --max-constexpr-depth=1 --max-constexpr-steps=2 --constexpr-backtrace-limit=4 --max-instance-array=5 --max-enum-values=100 --ignore-unknown-modules --relax-enum-conversions --allow-hierarchical-const --allow-dup-initial-drivers --lint-only --color-diagnostics=false --timescale=10ns/10ps 2>&1
// CHECK: Build succeeded
// CHECK: Build succeeded
// CHECK: Build succeeded

// RUN: %slang %s %data/test2.sv -I %data --single-unit --lint-only 2>&1
// CHECK: Build succeeded

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
