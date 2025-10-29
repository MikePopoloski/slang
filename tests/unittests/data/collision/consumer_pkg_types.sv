package consumer_pkg_types;
  import type_forward_a_pkg::*;
  import type_forward_b_pkg::*;
  typedef foo_t consumer_foo_t;
endpackage

module consumer_types_top;
  import consumer_pkg_types::*;
  consumer_foo_t dummy;
endmodule
