module chain_loop (
  input logic i_value,
  output logic o_value
);

  parameter p_stages = 4;

  logic pipeline [p_stages-1:0];

  assign pipeline[0] = i_value;

  always_comb begin
    for (int i=1; i<p_stages; i++) begin
      pipeline[i] = pipeline[i-1];
    end
  end

  assign o_value = pipeline[p_stages-1];

endmodule
