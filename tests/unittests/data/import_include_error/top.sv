`define MAKE_UNIT(idx_expr) compute_unit #(`include "shared_assign.sv", .INDEX(idx_expr))

module top;
  localparam int WIDTH  = 4;
  localparam bit ENABLE = 1;
  logic [WIDTH-1:0] result;

  `MAKE_UNIT(0) u_result (.value_o(result));
endmodule
