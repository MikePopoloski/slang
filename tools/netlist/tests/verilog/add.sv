module test (
  input logic i_a,
  input logic i_b,
  output logic [1:0] o_sum
);
  assign o_sum = i_a + i_b;
endmodule
