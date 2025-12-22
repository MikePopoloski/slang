module paramTest1 ();
    parameter P = P;
endmodule

module paramTest2 ();
    parameter P = P1;
    parameter P1 = P;
endmodule

module paramTest3 #(parameter W = WIDTH) ();
    parameter WIDTH = BITS * W;
    localparam BITS = (WIDTH * DEPTH) - 1;
    parameter DEPTH = 2;
endmodule

module paramTest4(input logic [W-1:0] a, logic [$bits(a)-1:0] b);
    logic [3:0] c;
    function int foo;
        return $bits(b);
    endfunction
    parameter W = $bits(c) + foo();
endmodule

module paramTest5(input logic [W-1:0] a, logic [$bits(a)-1:0] b);
    logic [3:0] c;
    function int foo;
        parameter W = C;
        return $bits(b) + W;
    endfunction
    parameter W = $bits(c) + foo();

    parameter C = W + foo();
endmodule
