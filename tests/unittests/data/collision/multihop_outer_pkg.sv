package multihop_outer_pkg;
  import multihop_mid_pkg::*;
  // Second hop forwards WIDTH via the intermediate package.
  localparam int unsigned WIDTH = multihop_mid_pkg::WIDTH;
endpackage
