module chain_sequence(
  input logic i_value,
  output logic o_value
);

  logic a, b, c, d;

  always_comb begin
    a = i_value;
    b = a;
    c = b;
  end

  assign o_value = c;

endmodule
