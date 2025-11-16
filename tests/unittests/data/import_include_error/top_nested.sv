`define INNER(idx_expr) \
  dual_compute_unit #(`include "dual_param_width.sv" \
                      `include "dual_param_enable.sv" \
                      .INDEX(idx_expr)) \
  inner``idx_expr();

`define OUTER(idx_expr0, idx_expr1) \
  `INNER(idx_expr0) \
  `INNER(idx_expr1)

module top_nested;
  localparam int WIDTH  = 4;
  localparam bit ENABLE = 1;

  `OUTER(0, 1)
endmodule
