module dual_compute_unit
  #(parameter int WIDTH = 1,
    parameter bit ENABLE = 0,
    parameter int INDEX = 0);

  generate
    if (WIDTH + (ENABLE ? 1 : 0) + INDEX >= 0) begin
    end
  endgenerate
endmodule
