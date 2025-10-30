`define MAKE_DUAL(idx_expr) \
  dual_compute_unit #(`include "dual_param_width.sv" \
                      `include "dual_param_enable.sv" \
                      .INDEX(idx_expr)) \
  u``idx_expr();

module top_dual;
  localparam int WIDTH  = 4;
  localparam bit ENABLE = 1;

  `MAKE_DUAL(0)
  `MAKE_DUAL(1)
endmodule
