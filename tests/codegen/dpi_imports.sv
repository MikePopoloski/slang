// Tests for DPI import codegen: IR structure verification.
// REQUIRES: llvm
// RUN: %slang --emit-ir - %s

// Global string constants for string-typed DPI arguments are emitted
// as null-terminated private constants before any declarations.
// CHECK: private unnamed_addr constant

// ============================================================
// String argument (const char*)
// ============================================================

// CHECK-LABEL: declare i32 @puts(ptr)
// CHECK-LABEL: define private i32 @call_puts
// CHECK: call i32 @puts(ptr @
// CHECK: ret i32
import "DPI-C" function int puts(string s);
function automatic int call_puts();
    return puts("hello");
endfunction

// ============================================================
// Integer arguments and return types
// ============================================================

// CHECK-LABEL: declare i32 @add_ints(i32, i32)
// CHECK-LABEL: define private i32 @test_add_ints
// CHECK: call i32 @add_ints(i32 3, i32 4)
// CHECK: ret i32
import "DPI-C" function int add_ints(int a, int b);
function automatic int test_add_ints();
    return add_ints(3, 4);
endfunction

// CHECK-LABEL: declare i8 @get_byte(i8)
import "DPI-C" function byte get_byte(byte b);

// CHECK-LABEL: declare i16 @get_short(i16)
import "DPI-C" function shortint get_short(shortint x);

// CHECK-LABEL: declare i64 @get_long(i64)
import "DPI-C" function longint get_long(longint x);

// ============================================================
// Floating-point arguments and return types
// The C alias 'fabs' is used as the symbol name; the SV name is 'c_fabs'.
// ============================================================

// CHECK-LABEL: declare double @fabs(double)
// CHECK-LABEL: define private double @test_fabs
// CHECK: call double @fabs(double
// CHECK: ret double
import "DPI-C" fabs = function real c_fabs(real x);
function automatic real test_fabs(real v);
    return c_fabs(v);
endfunction

// CHECK-LABEL: declare float @fabsf(float)
import "DPI-C" function shortreal fabsf(shortreal x);

// ============================================================
// Void return (no return value)
// ============================================================

// CHECK-LABEL: declare void @print_int(i32)
import "DPI-C" function void print_int(int x);

// ============================================================
// C identifier alias
// ============================================================

// CHECK-LABEL: declare i32 @my_c_func(i32)
import "DPI-C" my_c_func = function int sv_name(int x);
