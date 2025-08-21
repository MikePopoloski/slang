module test_formatting();
    // Constants that should be flagged
    logic [7:0] val1 = 255;  // Should require 8'hFF
    logic [3:0] val2 = 15;   // Should require 4'hF
    
    // Constants that should NOT be flagged (bit selects)
    logic [7:0] bus;
    logic bit1 = bus[7];     // 7 should not be flagged
    logic [3:0] bits = bus[7:4];  // 7 and 4 should not be flagged
    
    // Array dimensions that should NOT be flagged  
    logic [7:0] mem [0:255];  // 7, 0, 0, 255 should not be flagged
    
    // Parameter that should NOT be flagged
    parameter WIDTH = 8;
    
    // For loop bounds that should NOT be flagged
    genvar i;
    for (i = 0; i < 8; i++) begin : gen_loop
        // Generate content
    end
    
    // Regular constants that should be flagged
    logic [15:0] big_val = 65535;  // Should require 16'hFFFF
    
endmodule