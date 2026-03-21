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

// ============================================================
// output int -> ptr
// ============================================================
// CHECK-LABEL: declare void @dpi_out_int(ptr)
import "DPI-C" function void dpi_out_int(output int x);

// ============================================================
// inout int -> ptr
// ============================================================
// CHECK-LABEL: declare void @dpi_inout_int(ptr)
import "DPI-C" function void dpi_inout_int(inout int x);

// ============================================================
// Mixed: input int, output int, inout int
// ============================================================
// CHECK-LABEL: declare void @dpi_mixed(i32, ptr, ptr)
import "DPI-C" function void dpi_mixed(input int a, output int b, inout int c);

// ============================================================
// output byte -> ptr
// ============================================================
// CHECK-LABEL: declare void @dpi_out_byte(ptr)
import "DPI-C" function void dpi_out_byte(output byte b);

// ============================================================
// output real -> ptr
// ============================================================
// CHECK-LABEL: declare void @dpi_out_real(ptr)
import "DPI-C" function void dpi_out_real(output real r);

// ============================================================
// Packed array arguments -> ptr
// ============================================================
// CHECK-LABEL: declare void @packed_array_func(ptr)
import "DPI-C" function void packed_array_func(bit [31:0] arr);

// ============================================================
// Packed struct -> ptr
// ============================================================
typedef struct packed {
    logic [7:0] a;
    logic [7:0] b;
} packed_struct_t;

// CHECK-LABEL: declare void @packed_struct_func(ptr)
import "DPI-C" function void packed_struct_func(packed_struct_t s);

// ============================================================
// Unpacked struct -> ptr
// ============================================================
typedef struct {
    int x;
    int y;
} unpacked_struct_t;

// CHECK-LABEL: declare void @unpacked_struct_func(ptr)
import "DPI-C" function void unpacked_struct_func(unpacked_struct_t s);

// ============================================================
// Fixed-size unpacked array -> ptr
// ============================================================
// CHECK-LABEL: declare void @fixed_array_func(ptr)
import "DPI-C" function void fixed_array_func(int arr [4]);

// ============================================================
// Open array -> ptr (svOpenArrayHandle)
// ============================================================
// CHECK-LABEL: declare void @open_array_func(ptr)
import "DPI-C" function void open_array_func(int arr []);

// ============================================================
// 4-state integer -> ptr (svLogicVecVal*)
// ============================================================
// CHECK-LABEL: declare void @integer_func(ptr)
import "DPI-C" function void integer_func(integer x);

// ============================================================
// 4-state time -> ptr (svLogicVecVal*)
// ============================================================
// CHECK-LABEL: declare void @time_func(ptr)
import "DPI-C" function void time_func(time t);

// ============================================================
// Scalar bit type (input) -> i8
// ============================================================
// CHECK-LABEL: declare void @bit_func(i8)
import "DPI-C" function void bit_func(bit b);

// ============================================================
// Scalar logic type (input) -> i8
// ============================================================
// CHECK-LABEL: declare void @logic_func(i8)
import "DPI-C" function void logic_func(logic l);

// ============================================================
// Chandle -> ptr
// ============================================================
// CHECK-LABEL: declare void @chandle_func(ptr)
import "DPI-C" function void chandle_func(chandle h);

// ============================================================
// bit (i1 internal) -> i8 at call site via zext
// ============================================================
// CHECK-LABEL: declare i8 @dpi_bit_identity(i8)
// CHECK-LABEL: define private i1 @call_bit_identity
// CHECK: zext i1
// CHECK: call i8 @dpi_bit_identity(i8
// CHECK: trunc i8
// CHECK: ret i1
import "DPI-C" function bit dpi_bit_identity(bit b);
function automatic bit call_bit_identity(bit v);
    return dpi_bit_identity(v);
endfunction

// ============================================================
// logic (i2 internal) -> i8 at call site via zext
// ============================================================
// CHECK-LABEL: declare i8 @dpi_logic_identity(i8)
// CHECK-LABEL: define private i2 @call_logic_identity
// CHECK: zext i2
// CHECK: call i8 @dpi_logic_identity(i8
// CHECK: trunc i8
// CHECK: ret i2
import "DPI-C" function logic dpi_logic_identity(logic l);
function automatic logic call_logic_identity(logic v);
    return dpi_logic_identity(v);
endfunction
