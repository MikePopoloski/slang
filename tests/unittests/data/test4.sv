module baz;
    int k = j;
    int j = 1;

`ifndef FOOBAR
    int blah = unknown;
`endif
endmodule

module unused;
    `pragma diagnostic warn="-Wfoobaz"
endmodule

`ifdef FOOBAR
module frob #(parameter int bar);
endmodule
`endif
