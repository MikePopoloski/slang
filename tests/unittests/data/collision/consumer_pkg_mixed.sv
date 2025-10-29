package consumer_pkg_mixed;
  import a_pkg::*;
  import b_pkg::*;

  // WIDTH forwards cleanly through both packages.
  typedef logic [WIDTH-1:0] addr_t;
  // DEPTH is ambiguous because b_pkg changes it.
  typedef logic [DEPTH-1:0] data_t;
endpackage

module consumer_mixed_top;
  import consumer_pkg_mixed::*;
  addr_t addr;
  data_t data;
endmodule
