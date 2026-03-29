// Test file for --incdir-first / VCS compat mode include search order.
// Includes incdir_shadow.svh, which exists in both the local data/ directory
// and in data/nested/ (used as a +incdir directory in the tests).
//
// If the LOCAL file is found, INCDIR_SHADOW_IS_LOCAL is defined, and a
// deliberate undefined-identifier error is triggered to make compilation fail.
// If the INCDIR file (nested/) is found, no error is triggered and the module
// compiles cleanly.
`include "incdir_shadow.svh"

module incdir_first_test;
`ifdef INCDIR_SHADOW_IS_LOCAL
    // Local shadow file was found -- trigger a deliberate error:
    int x = local_was_found_error;
`else
    int x = 1;
`endif
endmodule
