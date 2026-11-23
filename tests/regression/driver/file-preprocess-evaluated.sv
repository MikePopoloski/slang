// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// RUN: %slang -E --directives %s 2>&1
// RUN: %slang -E --directives %s > %t.sv && %slang --quiet --parse-only %t.sv
// CHECK-NOT: {{define|undef|ifdef|ifndef|elsif|else|endif|inactive}}
// CHECK: {{^}}`timescale 1ns/1ps{{$}}
// CHECK-NEXT: {{^}}module top;{{$}}
// CHECK-NEXT: {{^}}    localparam int width = 4;{{$}}
// CHECK-NEXT: {{^}}    localparam int nested = 1;{{$}}
// CHECK-NEXT: {{^}}    localparam int last = 2;{{$}}
// CHECK-NEXT: {{^}}endmodule{{$}}
// CHECK-NEXT: {{^}}`default_nettype wire{{$}}

`timescale 1ns/1ps
`define WIDTH 4 // trailing
`define ENABLED
module top;
    `ifdef ENABLED // taken
    localparam int width = `WIDTH;
        `ifndef MISSING
    localparam int nested = 1;
        `else
    localparam int inactive_a = 0;
        `endif
    `elsif OTHER
    localparam int inactive_b = 0;
    `else
    localparam int inactive_c = 0;
    `endif // ENABLED
    `undef WIDTH
    `undefineall
    localparam int last = 2;
endmodule
`default_nettype wire
