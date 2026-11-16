// DEFAULT

 
 
module child;
    localparam int width = 3;
endmodule
module top;
    localparam int value = 17;
    localparam int sum = ((3)  + 17);
    localparam int continued_value = 17;
    localparam int continued_expr = (17  
);
    logic signal2;
    string source_name = "preprocess_directives.sv";
    localparam int source_line = 18;
endmodule

// COMMENTS

 // Value definition
 /* Macro end */
// Included module
module child;
    localparam int width = 3;
endmodule
module top;
    localparam int value = 17;
    localparam int sum = ((3) /* Macro middle */ + 17);
    localparam int continued_value = 17;
    localparam int continued_expr = (17 /* Comment before continuation */ 
);
    logic signal2;
    string source_name = "preprocess_directives.sv";
    localparam int source_line = 18;
endmodule

// DIRECTIVES
`line 1 "preprocess_directives.sv" 0
`timescale 1ns/1ps
`default_nettype none
`define VALUE 17 
`define JOIN(a, b) a``b
`define ADD_VALUE(x)  ((x)  + `VALUE) 
`define CONTINUED_VALUE 17  \
`define CONTINUED_EXPR (17  \
)
`define WIDTH 3
module child;
    localparam int width = 3;
endmodule
module top;
    localparam int value = 17;
    localparam int sum = ((3)  + 17);
    localparam int continued_value = 17;
    localparam int continued_expr = (17  
);
    logic signal2;
    string source_name = "preprocess_directives.sv";
    localparam int source_line = 18;
endmodule
`default_nettype wire

// COMMENTS-AND-DIRECTIVES
`line 1 "preprocess_directives.sv" 0
`timescale 1ns/1ps
`default_nettype none
`define VALUE 17 // Value definition
`define JOIN(a, b) a``b
`define ADD_VALUE(x) /* Macro beginning */ ((x) /* Macro middle */ + `VALUE) /* Macro end */
`define CONTINUED_VALUE 17 /* Continued macro end */ \
`define CONTINUED_EXPR (17 /* Comment before continuation */ \
)
`define WIDTH 3
// Included module
module child;
    localparam int width = 3;
endmodule
module top;
    localparam int value = 17;
    localparam int sum = ((3) /* Macro middle */ + 17);
    localparam int continued_value = 17;
    localparam int continued_expr = (17 /* Comment before continuation */ 
);
    logic signal2;
    string source_name = "preprocess_directives.sv";
    localparam int source_line = 18;
endmodule
`default_nettype wire

