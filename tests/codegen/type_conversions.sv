// Tests for type conversion / cast codegen.
// REQUIRES: llvm
// RUN: %slang --emit-ir - %s

// CHECK-LABEL: define private double @int_to_real
// CHECK: sitofp i32 {{.*}} to double
// CHECK: ret double

// CHECK-LABEL: define private i32 @real_to_int
// CHECK: call double @llvm.round.f64
// CHECK: llvm.fptosi.sat.i32.f64
// CHECK: ret i32

// CHECK-LABEL: define private float @real_to_shortreal
// CHECK: fptrunc double {{.*}} to float
// CHECK: ret float

function automatic real int_to_real(int x);
    return real'(x);
endfunction

function automatic int real_to_int(real x);
    return int'(x);
endfunction

function automatic shortreal real_to_shortreal(real x);
    return shortreal'(x);
endfunction

// ---------------------------------------------------------------------------
// Integer-to-integer: 2-state resize
// ---------------------------------------------------------------------------

// CHECK-LABEL: define private i8 @int_to_byte_trunc
// CHECK: trunc i32 {{.*}} to i8
// CHECK: ret i8
function automatic byte int_to_byte_trunc(int x);
    return byte'(x);
endfunction

// CHECK-LABEL: define private i64 @int_to_longint_sext
// Signed int extended to signed longint -- sign extend.
// CHECK: sext i32 {{.*}} to i64
// CHECK: ret i64
function automatic longint int_to_longint_sext(int x);
    return longint'(x);
endfunction

// CHECK-LABEL: define private i64 @uint_to_longint_zext
// Unsigned int extended to longint -- zero extend (source is unsigned).
// CHECK: zext i32 {{.*}} to i64
// CHECK: ret i64
function automatic longint uint_to_longint_zext(int unsigned x);
    return longint'(x);
endfunction

// CHECK-LABEL: define private i32 @byte_to_int_sext
// Signed byte extended to signed int -- sign extend.
// CHECK: sext i8 {{.*}} to i32
// CHECK: ret i32
function automatic int byte_to_int_sext(byte x);
    return int'(x);
endfunction

// CHECK-LABEL: define private i32 @ubyte_to_int_zext
// Unsigned byte to int -- zero extend.
// CHECK: zext i8 {{.*}} to i32
// CHECK: ret i32
function automatic int ubyte_to_int_zext(byte unsigned x);
    return int'(x);
endfunction

// ---------------------------------------------------------------------------
// Integer-to-integer: 4-state to 2-state (flatten unknowns)
// ---------------------------------------------------------------------------

// CHECK-LABEL: define private i32 @logic_to_int
// CHECK: lshr i64
// CHECK: trunc i64 {{.*}} to i32
// CHECK: and i32
// CHECK: ret i32
function automatic int logic_to_int(logic [31:0] x);
    return int'(x);
endfunction

// CHECK-LABEL: define private i8 @logic8_to_byte
// 4-state -> 2-state with truncation.
// CHECK: ret i8
function automatic byte logic8_to_byte(logic [7:0] x);
    return byte'(x);
endfunction

// ---------------------------------------------------------------------------
// Integer-to-integer: 2-state to 4-state
// ---------------------------------------------------------------------------

// CHECK-LABEL: define private i64 @int_to_logic32
// CHECK: zext i32 {{.*}} to i64
// CHECK: ret i64
function automatic logic [31:0] int_to_logic32(int x);
    return x;
endfunction

// ---------------------------------------------------------------------------
// Integer-to-integer: Propagated sign extension
// ---------------------------------------------------------------------------

// CHECK-LABEL: define private i64 @propagated_sext
// CHECK: sext i32 {{.*}} to i64
// CHECK: ret i64
function automatic longint propagated_sext(int a);
    longint x = a;  // implicit conversion, sign-extends because source is signed
    return x;
endfunction

// ---------------------------------------------------------------------------
// Integer-to-float
// ---------------------------------------------------------------------------

// CHECK-LABEL: define private double @byte_to_real
// CHECK: sitofp i8 {{.*}} to double
// CHECK: ret double
function automatic real byte_to_real(byte x);
    return real'(x);
endfunction

// CHECK-LABEL: define private float @int_to_shortreal
// CHECK: sitofp i32 {{.*}} to float
// CHECK: ret float
function automatic shortreal int_to_shortreal(int x);
    return shortreal'(x);
endfunction

// CHECK-LABEL: define private double @uint_to_real
// CHECK: uitofp i32 {{.*}} to double
// CHECK: ret double
function automatic real uint_to_real(int unsigned x);
    return real'(x);
endfunction

// CHECK-LABEL: define private double @logic_to_real
// CHECK: lshr
// CHECK: and i32
// CHECK: {{s|u}}itofp i32 {{.*}} to double
// CHECK: ret double
function automatic real logic_to_real(logic [31:0] x);
    return real'(x);
endfunction

// ---------------------------------------------------------------------------
// Float-to-integer: rounding
// ---------------------------------------------------------------------------

// CHECK-LABEL: define private i64 @real_to_longint
// CHECK: call double @llvm.round.f64
// CHECK: llvm.fptosi.sat.i64.f64
// CHECK: ret i64
function automatic longint real_to_longint(real x);
    return longint'(x);
endfunction

// CHECK-LABEL: define private i8 @real_to_byte
// CHECK: call double @llvm.round.f64
// CHECK: llvm.fptosi.sat.i8.f64
// CHECK: ret i8
function automatic byte real_to_byte(real x);
    return byte'(x);
endfunction

// CHECK-LABEL: define private i32 @shortreal_to_int
// CHECK: call float @llvm.round.f32
// CHECK: llvm.fptosi.sat.i32.f32
// CHECK: ret i32
function automatic int shortreal_to_int(shortreal x);
    return int'(x);
endfunction

// ---------------------------------------------------------------------------
// --run tests: correct evaluation of corner-case numeric conversions.
// Patterns use {{^VALUE$}} anchors so they only match the single-line JIT
// output, not incidental occurrences of the value in the --emit-ir output.
// ---------------------------------------------------------------------------

// --- Integer truncation: int -> signed byte ----------------------------------

// RUN: %slang --run conv_byte_trunc_128 %s
// CHECK: -8'sd128
// 128 = 0x80; low 8 bits interpreted as signed byte = -128.
function automatic byte conv_byte_trunc_128();
    return byte'(128);
endfunction

// RUN: %slang --run conv_byte_trunc_255 %s
// CHECK: -8'sd1
// 255 = 0xFF; low 8 bits interpreted as signed byte = -1.
function automatic byte conv_byte_trunc_255();
    return byte'(255);
endfunction

// RUN: %slang --run conv_byte_trunc_300 %s
// CHECK: 8'sd44
// 300 = 0x12C; low 8 bits 0x2C = 44 (positive, no sign change).
function automatic byte conv_byte_trunc_300();
    return byte'(300);
endfunction

// RUN: %slang --run conv_byte_neg_wrap %s
// CHECK: 8'sd127
// -129 = 0xFFFFFF7F; low 8 bits 0x7F = 127.
function automatic byte conv_byte_neg_wrap();
    return byte'(-129);
endfunction

// --- Unsigned byte: int -> byte unsigned -------------------------------------

// RUN: %slang --run conv_ubyte_from_neg1 %s
// CHECK: 8'd255
// -1 (0xFFFFFFFF) truncated to 8 bits = 255 as unsigned byte.
function automatic byte unsigned conv_ubyte_from_neg1();
    return byte unsigned'(-1);
endfunction

// RUN: %slang --run conv_ubyte_overflow %s
// CHECK: 8'd0
// 256 (0x100) truncated to 8 bits = 0.
function automatic byte unsigned conv_ubyte_overflow();
    return byte unsigned'(256);
endfunction

// --- Real-to-int: rounding half away from zero (llvm.round semantics) -------

// RUN: %slang --run conv_real_to_int_half_pos %s
// CHECK: {{^1$}}
// 0.5 rounds to 1 (half away from zero).
function automatic int conv_real_to_int_half_pos();
    return int'(0.5);
endfunction

// RUN: %slang --run conv_real_to_int_half_neg %s
// CHECK: {{^-1$}}
// -0.5 rounds to -1 (half away from zero).
function automatic int conv_real_to_int_half_neg();
    return int'(-0.5);
endfunction

// RUN: %slang --run conv_real_to_int_round_pos %s
// CHECK: {{^3$}}
// 2.5 rounds to 3.
function automatic int conv_real_to_int_round_pos();
    return int'(2.5);
endfunction

// RUN: %slang --run conv_real_to_int_round_neg %s
// CHECK: {{^-3$}}
// -2.5 rounds to -3.
function automatic int conv_real_to_int_round_neg();
    return int'(-2.5);
endfunction

// RUN: %slang --run conv_real_to_int_trunc %s
// CHECK: {{^0$}}
// 0.4 is closer to 0 than to 1, so rounds to 0.
function automatic int conv_real_to_int_trunc();
    return int'(0.4);
endfunction

// --- Real-to-int: saturation on overflow ------------------------------------

// RUN: %slang --run conv_real_to_int_sat_max %s
// CHECK: 2147483647
// 1e18 >> INT_MAX; fptosi.sat clamps to 2^31-1.
function automatic int conv_real_to_int_sat_max();
    return int'(1.0e18);
endfunction

// RUN: %slang --run conv_real_to_int_sat_min %s
// CHECK: -2147483648
// -1e18 << INT_MIN; fptosi.sat clamps to -2^31.
function automatic int conv_real_to_int_sat_min();
    return int'(-1.0e18);
endfunction

// --- Real-to-byte: saturation -----------------------------------------------

// RUN: %slang --run conv_real_to_byte_sat_pos %s
// CHECK: 8'sd127
// 200.0 > 127; fptosi.sat.i8 clamps to byte max.
function automatic byte conv_real_to_byte_sat_pos();
    return byte'(200.0);
endfunction

// RUN: %slang --run conv_real_to_byte_sat_neg %s
// CHECK: -8'sd128
// -200.0 < -128; fptosi.sat.i8 clamps to byte min.
function automatic byte conv_real_to_byte_sat_neg();
    return byte'(-200.0);
endfunction

// RUN: %slang --run conv_real_neg_zero %s
// CHECK: {{^0$}}
// -0.0 and 0.0 are equal by IEEE 754; fptosi converts to 0.
function automatic int conv_real_neg_zero();
    return int'(-0.0);
endfunction

// --- Sign / zero extension --------------------------------------------------

// RUN: %slang --run conv_int_neg_to_longint %s
// CHECK: -64'sd1
// -1 (32-bit signed) sign-extends to longint -1.
function automatic longint conv_int_neg_to_longint();
    return longint'(-1);
endfunction

// RUN: %slang --run conv_uint_max_to_longint_u %s
// CHECK: 64'hffffffff
// 32'hFFFFFFFF zero-extends to 64-bit unsigned 4294967295.
function automatic longint unsigned conv_uint_max_to_longint_u();
    return longint unsigned'(32'hFFFFFFFF);
endfunction

// --- Logic-to-int: unknown-bit flattening -----------------------------------

// RUN: %slang --run conv_logic_to_int_ones %s
// CHECK: {{^-1$}}
// 32'hFFFF_FFFF has no unknown bits; value bits all-ones -> int -1.
function automatic int conv_logic_to_int_ones();
    logic [31:0] v = 32'hFFFF_FFFF;
    return int'(v);
endfunction

// RUN: %slang --run conv_logic_to_int_unknowns %s
// CHECK: {{^0$}}
// 32'bx: all bits unknown; they flatten to 0 on 4-state -> 2-state cast.
function automatic int conv_logic_to_int_unknowns();
    logic [31:0] v = 32'bx;
    return int'(v);
endfunction
