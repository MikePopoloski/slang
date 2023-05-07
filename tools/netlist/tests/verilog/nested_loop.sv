module test #(localparam N=4) (
  input logic i_value,
  output logic o_value);

  logic [(N*2)-1:0] stages;

  assign stages[0] = i_value;
  assign o_value = stages[1];

  always_comb begin
    for (int i=1; i<N-1; i++) begin
      for (int j=1; j<N-1; j++) begin
        stages[(i*N + j)] = stages[(i*N + j)-1];
      end
    end
  end

endmodule

