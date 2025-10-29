package a_pkg;
  import consts_pkg::*;
  // Forward WIDTH by mirroring the definition from consts_pkg without changing it.
  localparam int unsigned WIDTH = consts_pkg::WIDTH;
  // DEPTH also forwards unchanged.
  localparam int unsigned DEPTH = consts_pkg::DEPTH;
endpackage
