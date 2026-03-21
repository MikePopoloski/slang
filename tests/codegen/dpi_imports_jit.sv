// JIT execution tests for DPI import codegen.
// Verifies that DPI-imported C functions are correctly called at runtime.
// REQUIRES: llvm

// RUN: %slang --run dpi_puts %s
// CHECK: hello from DPI

// RUN: %slang --run dpi_abs %s
// CHECK: 42

// RUN: %slang --run dpi_fabs %s
// CHECK: 3.14

// RUN: %slang --run dpi_fabsf %s
// CHECK: 2.5

// ---- string argument: puts ----
// Call the C 'puts' function via DPI-C with a string literal argument.
// puts writes its argument followed by a newline to stdout; the JIT should
// resolve the symbol from libc and execute it correctly.
import "DPI-C" function int puts(string s);
function automatic int dpi_puts();
    return puts("hello from DPI");
endfunction

// ---- integer argument / return: abs ----
// C 'abs' takes int and returns int.
import "DPI-C" function int abs(int x);
function automatic int dpi_abs();
    return abs(-42);
endfunction

// ---- real (double) argument / return: fabs ----
import "DPI-C" function real fabs(real x);
function automatic real dpi_fabs();
    return fabs(-3.14);
endfunction

// ---- shortreal (float) argument / return: fabsf via C alias ----
import "DPI-C" fabsf = function shortreal dpi_fabsf_sv(shortreal x);
function automatic shortreal dpi_fabsf();
    return dpi_fabsf_sv(-2.5);
endfunction
