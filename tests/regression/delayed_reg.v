module delayed_reg (input in, output out);

    always @(posedge in) begin
        #10 out = !out;
    end

endmodule
