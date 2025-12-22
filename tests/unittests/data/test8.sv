module paramTest1 ();
    parameter P = P1;
    parameter P1 = 1;
    wire p = w;
    wire w = 1;

    specparam tAC = tBC;
    specparam tBC = 10;
endmodule

module paramTest2 #(parameter W = WIDTH) ();
    parameter WIDTH = BITS * 2;
    localparam BITS = (DEPTH * DEPTH) - 1;
    parameter DEPTH = 2;
endmodule

module paramTest3(input logic [3-1:0] a, logic [$bits(a)-1:0] b);
    logic [3:0] c;
    function int foo;
        return $bits(b);
    endfunction
    parameter W = $bits(c) + foo();
    parameter C = W + foo();
endmodule

module paramTest4(input logic [C-1:0] a, logic [$bits(a)-1:0] b);
    logic [3:0] c;
    function int foo;
        parameter W = C;
        return $bits(b) + W;
    endfunction
    parameter W = $bits(c) + foo();
    parameter A = C + W;
    parameter C = 1;
endmodule
