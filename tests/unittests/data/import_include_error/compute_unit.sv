module compute_unit
  #(`include "shared_decl.sv",
    parameter int INDEX = 0)
  (output logic [WIDTH-1:0] value_o);

  localparam int _unused_index = INDEX;
  assign value_o = {WIDTH{ENABLE}};
endmodule
