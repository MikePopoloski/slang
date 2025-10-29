package consumer_pkg_multihop;
  import multihop_mid_pkg::*;
  import multihop_outer_pkg::*;
  localparam int unsigned WIDTH_MIRROR = WIDTH;
endpackage

module consumer_multihop_top;
  import consumer_pkg_multihop::*;
  logic [WIDTH_MIRROR-1:0] dummy;
endmodule
