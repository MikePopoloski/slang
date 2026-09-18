// Exercises preprocessor conditional directives so the CST JSON round-trip covers the
// trivia handling of disabled branches (line breaks, indentation, and comments that end
// a skipped branch must still round-trip faithfully).

`include "conditionals_include.svh"

module m;
`ifdef FOO
    logic disabled_simple;
`endif

`ifndef FOO
    logic taken_simple;
`else
    logic disabled_else;
`endif

`ifdef FOO
    logic a;
`elsif BAR
    logic b;
`else
    logic c;
`endif

`ifndef FOO
    // taken branch with a nested disabled block
    `ifdef BAZ
        logic nested_disabled;
    `else
        logic nested_taken;
    `endif
`endif

`ifdef FOO
    // disabled branch containing comments and a nested pair
    logic x; // trailing comment
    `ifdef INNER
        logic y;
    `endif
    // dangling comment before endif
`endif

// A macro whose body itself contains conditional directives. In the FOO-defined test
// variants its invocation produces expanded directive trivia that must not be
// double-counted when reconstructing the original source.
`define GUARD(name) \
    `ifndef name \
        `define name \
    `endif

`ifdef FOO
    `GUARD(SOMETHING)
`endif

endmodule
