// Round-trip DPI test for the --sv_lib flag.
//
// Verifies the full call chain:
//   SV (run_test) --> C (c_combine) --> SV (sv_add) --> C --> SV
//
// The C helper calls sv_add, an SV function exported via DPI-C. The result
// proves that:
//   1. The .o loaded via --sv_lib is linked into the JIT, and
//   2. Symbols exported from the SV module are visible to that object.
//
// REQUIRES: llvm, sv_lib_helper_o

// The helper object is pre-compiled by CMake and its path is passed to
// this test via the --define sv_lib_helper_o=... flag. This avoids invoking
// a platform-specific C compiler from within the test itself.
// RUN: %slang --sv_lib %sv_lib_helper_o --run run_test %s
// CHECK: 19

function automatic int sv_add(int a, int b);
    return a + b;
endfunction
export "DPI-C" function sv_add;

import "DPI-C" function int c_combine(int a, int b);

function automatic int run_test();
    return c_combine(3, 4);
endfunction
