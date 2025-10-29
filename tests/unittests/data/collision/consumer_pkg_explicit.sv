package consumer_pkg_explicit;
  import explicit_forward_pkg::*;
  import explicit_import_pkg::*;
  localparam int unsigned WIDTH_MIRROR = WIDTH;
endpackage

module consumer_explicit_top;
  import consumer_pkg_explicit::*;
  logic [WIDTH_MIRROR-1:0] dummy;
endmodule
