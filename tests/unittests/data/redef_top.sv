// Instantiates mux_primitive. When --allow-module-redef is used the module
// version (from redef_module.sv) is kept and this compiles cleanly.
module redef_top;
  logic S, A, B, Y;
  mux_primitive prim(Y, S, A, B);
endmodule
