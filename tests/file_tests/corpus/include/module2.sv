module helper
#(
    parameter int W = 8
)
(
    input  logic [W-1:0]   foo,
    output logic [W-1:0]   bar
);

    always_comb bar = ~foo;

endmodule


module module2
#(
    parameter int P1 = 4,
    parameter int P2 = 5
)
(
    input  logic [P1-1:0]   in1,
    input  logic [P2-1:0]   in2,
    input  logic [3:0]      in3,

    output logic [P1-1:0]   out1,
    output logic [P2-1:0]   out2,
    output logic [3:0]      out3
);

    helper #(.W(4)) helper1 (
        .foo (in1),
        .bar (out1)
    );

    helper #(.W(P2)) helper2 (
        .foo (in2),
        .bar (out2)
    );

    always_comb out3 = in3;

endmodule
