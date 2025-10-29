package b_pkg;
  import consts_pkg::*;
  // Forward WIDTH by mirroring the definition from consts_pkg without changing it.
  localparam int unsigned WIDTH = consts_pkg::WIDTH;
  // Modify DEPTH so it conflicts when both packages are imported.
  localparam int unsigned DEPTH = consts_pkg::DEPTH + 4;
endpackage
