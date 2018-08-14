module delayed_reg (input in, output out);

    reg out;

    always @(posedge in) begin
        #10 out = !out;
    end

endmodule
