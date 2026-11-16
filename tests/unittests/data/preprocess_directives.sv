`line 1 "preprocess_directives.sv" 0
`timescale 1ns/1ps
`default_nettype none
`define VALUE 17 // Value definition
`define JOIN(a, b) a``b
`define ADD_VALUE(x) /* Macro beginning */ ((x) /* Macro middle */ + `VALUE) /* Macro end */
`define CONTINUED_VALUE 17 /* Continued macro end */ \

`define CONTINUED_EXPR (17 /* Comment before continuation */ \
)
`include "preprocess_header.svh"
module top;
    localparam int value = `VALUE;
    localparam int sum = `ADD_VALUE(3 /* Argument comment */);
    localparam int continued_value = `CONTINUED_VALUE;
    localparam int continued_expr = `CONTINUED_EXPR;
    logic `JOIN(signal, 2);
    string source_name = `__FILE__;
    localparam int source_line = `__LINE__;
endmodule
`default_nettype wire
