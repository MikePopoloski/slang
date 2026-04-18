// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// Mapping *.v files to Verilog 1364-2005 keywords allows using reserved
// SystemVerilog words (e.g. 'do') as identifiers inside those files.
// RUN: %slang --map-keyword-version "1364-2005+%data/*.v" -I %data/ %s 2>&1
// CHECK: Build succeeded

`include "verilog.v"

module m();

    wire a;

    always_comb begin
        $display(a);
    end

    t t1();

    m1 m2();

endmodule


// Providing two --map-keyword-version options that together force files to
// parse as older Verilog causes SystemVerilog constructs to be rejected.
// RUN: %slang --map-keyword-version "1364-2005+%data/*.v" --map-keyword-version "1364-2005+%s,%data/another_systemverilog.sv" %s 2>&1 || true
// CHECK: Build failed

// A value without a '+' separator is rejected at argument-parsing time.
// RUN: %slang --map-keyword-version "1364-2005+%data/*.v" --map-keyword-version=asdf --map-keyword-version "1364-2025+%s,%data/another_systemverilog.sv" %s 2>&1 || true
// CHECK: missing '+' in argument 'asdf'
// CHECK: '1364-2025' is not a valid keyword version
