`include "verilog.v"

module m();

    wire a;

    always_comb begin
        $display(a);
    end

    t t1();

    m1 m2();

endmodule
