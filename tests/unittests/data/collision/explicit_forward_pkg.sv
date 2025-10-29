package explicit_forward_pkg;
  import consts_pkg::*;
  // Re-export WIDTH via a localparam that forwards to the consts_pkg definition.
  localparam int unsigned WIDTH = consts_pkg::WIDTH;
endpackage
