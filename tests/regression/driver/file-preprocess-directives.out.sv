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
`line 1 "preprocess_header.svh" 0
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
`line 1 "preprocess_header.svh" 0
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

// LINES



 

 






`line 3 "preprocess_header.svh" 1
module child;
    localparam int width = 3;
endmodule

`line 11 "preprocess_directives.sv" 2
module top;
    localparam int value = 17;
    localparam int sum = ((3)  + 17);
    localparam int continued_value = 17;
    localparam int continued_expr = (17  
`line 15 "preprocess_directives.sv" 0
);
    logic signal2;
    string source_name = "preprocess_directives.sv";
    localparam int source_line = 18;
endmodule

// LINES-AND-COMMENTS



 // Value definition

 /* Macro end */





// Included module
`line 3 "preprocess_header.svh" 1
module child;
    localparam int width = 3;
endmodule

`line 11 "preprocess_directives.sv" 2
module top;
    localparam int value = 17;
    localparam int sum = ((3) /* Macro middle */ + 17);
    localparam int continued_value = 17;
    localparam int continued_expr = (17 /* Comment before continuation */ 
`line 15 "preprocess_directives.sv" 0
);
    logic signal2;
    string source_name = "preprocess_directives.sv";
    localparam int source_line = 18;
endmodule

// LINES-AND-DIRECTIVES

`line 1 "preprocess_directives.sv" 0
`timescale 1ns/1ps
`default_nettype none
`define VALUE 17 
`define JOIN(a, b) a``b
`define ADD_VALUE(x)  ((x)  + `VALUE) 
`define CONTINUED_VALUE 17  \

`define CONTINUED_EXPR (17  \
)

`line 1 "preprocess_header.svh" 1
`define WIDTH 3

module child;
    localparam int width = 3;
endmodule

`line 11 "preprocess_directives.sv" 2
module top;
    localparam int value = 17;
    localparam int sum = ((3)  + 17);
    localparam int continued_value = 17;
    localparam int continued_expr = (17  
`line 15 "preprocess_directives.sv" 0
);
    logic signal2;
    string source_name = "preprocess_directives.sv";
    localparam int source_line = 18;
endmodule
`default_nettype wire
// LINES-COMMENTS-AND-DIRECTIVES

`line 1 "preprocess_directives.sv" 0
`timescale 1ns/1ps
`default_nettype none
`define VALUE 17 // Value definition
`define JOIN(a, b) a``b
`define ADD_VALUE(x) /* Macro beginning */ ((x) /* Macro middle */ + `VALUE) /* Macro end */
`define CONTINUED_VALUE 17 /* Continued macro end */ \

`define CONTINUED_EXPR (17 /* Comment before continuation */ \
)

`line 1 "preprocess_header.svh" 1
`define WIDTH 3
// Included module
module child;
    localparam int width = 3;
endmodule

`line 11 "preprocess_directives.sv" 2
module top;
    localparam int value = 17;
    localparam int sum = ((3) /* Macro middle */ + 17);
    localparam int continued_value = 17;
    localparam int continued_expr = (17 /* Comment before continuation */ 
`line 15 "preprocess_directives.sv" 0
);
    logic signal2;
    string source_name = "preprocess_directives.sv";
    localparam int source_line = 18;
endmodule
`default_nettype wire
// LINES-AND-SOURCE



 

 






// preprocess_header.svh:3
`line 3 "preprocess_header.svh" 1
module child;
    localparam int width = 3;
endmodule

// preprocess_directives.sv:11
`line 11 "preprocess_directives.sv" 2
module top;
    localparam int value = 17;
    localparam int sum = ((3)  + 17);
    localparam int continued_value = 17;
    localparam int continued_expr = (17  
`line 15 "preprocess_directives.sv" 0
);
    logic signal2;
    string source_name = "preprocess_directives.sv";
    localparam int source_line = 18;
endmodule

// LINES-SOURCE-COMMENTS-AND-DIRECTIVES

// preprocess_directives.sv:1
`line 1 "preprocess_directives.sv" 0
`timescale 1ns/1ps
`default_nettype none
`define VALUE 17 // Value definition
`define JOIN(a, b) a``b
`define ADD_VALUE(x) /* Macro beginning */ ((x) /* Macro middle */ + `VALUE) /* Macro end */
`define CONTINUED_VALUE 17 /* Continued macro end */ \

`define CONTINUED_EXPR (17 /* Comment before continuation */ \
)

// preprocess_header.svh:1
`line 1 "preprocess_header.svh" 1
`define WIDTH 3
// Included module
module child;
    localparam int width = 3;
endmodule

// preprocess_directives.sv:11
`line 11 "preprocess_directives.sv" 2
module top;
    localparam int value = 17;
    localparam int sum = ((3) /* Macro middle */ + 17);
    localparam int continued_value = 17;
    localparam int continued_expr = (17 /* Comment before continuation */ 
`line 15 "preprocess_directives.sv" 0
);
    logic signal2;
    string source_name = "preprocess_directives.sv";
    localparam int source_line = 18;
endmodule
`default_nettype wire
