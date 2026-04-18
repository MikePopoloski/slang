// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang %s --libdir %data/library --libext .qv -Wno-foobar 2>&1 || true
// CHECK: unknown warning option
// CHECK: foobaz

// RUN: %slang %s --libdir %data/library --libext .qv --top=qq --single-unit --libraries-inherit-macros 2>&1
// CHECK: Build succeeded

module m;
    libmod lm();
endmodule

module n(I.m im);
endmodule

`define SOME_DEF
