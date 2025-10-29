package consumer_pkg;
  import a_pkg::*;
  import b_pkg::*;

  // Unqualified use is ambiguous: two imported decls named WIDTH exist
  typedef logic [WIDTH-1:0] addr_t;
endpackage

// Provide a trivial top so the driver tests don't trigger -Wmissing-top.
module consumer_top;
  import consumer_pkg::*;
  addr_t dummy;
endmodule
