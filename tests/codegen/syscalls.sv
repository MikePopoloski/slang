// Tests for built-in system call codegen.
// REQUIRES: llvm
// RUN: %slang --emit-ir - %s

// ============================================================
// Conversion functions
// ============================================================

// CHECK-LABEL: define private i32 @_SV0NvU9test_rtoi
// CHECK: llvm.fptosi.sat.i32.f64
// CHECK: ret i32
function automatic int test_rtoi(real r);
    return $rtoi(r);
endfunction

// CHECK-LABEL: define private double @_SV0NvU9test_itor
// CHECK: sitofp i32 {{.*}} to double
// CHECK: ret double
function automatic real test_itor(int i);
    return $itor(i);
endfunction

// CHECK-LABEL: define private i64 @_SV0NvU15test_realtobits
// CHECK: bitcast double {{.*}} to i64
// CHECK: ret i64
function automatic longint unsigned test_realtobits(real r);
    return $realtobits(r);
endfunction

// CHECK-LABEL: define private double @_SV0NvU15test_bitstoreal
// CHECK: bitcast i64 {{.*}} to double
// CHECK: ret double
function automatic real test_bitstoreal(longint unsigned b);
    return $bitstoreal(b);
endfunction

// CHECK-LABEL: define private i32 @_SV0NvU20test_shortrealtobits
// CHECK: bitcast float {{.*}} to i32
// CHECK: ret i32
function automatic int unsigned test_shortrealtobits(shortreal r);
    return $shortrealtobits(r);
endfunction

// CHECK-LABEL: define private float @_SV0NvU20test_bitstoshortreal
// CHECK: bitcast i32 {{.*}} to float
// CHECK: ret float
function automatic shortreal test_bitstoshortreal(int unsigned b);
    return $bitstoshortreal(b);
endfunction

// ============================================================
// Integer math: $clog2
// ============================================================

// CHECK-LABEL: define private i32 @_SV0NvU10test_clog2
// CHECK: llvm.ctlz.i32
// CHECK: ret i32
function automatic int test_clog2(int unsigned n);
    return $clog2(n);
endfunction

// ============================================================
// Floating-point math — LLVM intrinsics
// ============================================================

// CHECK-LABEL: define private double @_SV0NvU7test_ln
// CHECK: call double @llvm.log.f64
// CHECK: ret double
function automatic real test_ln(real x);
    return $ln(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU10test_log10
// CHECK: call double @llvm.log10.f64
// CHECK: ret double
function automatic real test_log10(real x);
    return $log10(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU8test_exp
// CHECK: call double @llvm.exp.f64
// CHECK: ret double
function automatic real test_exp(real x);
    return $exp(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU9test_sqrt
// CHECK: call double @llvm.sqrt.f64
// CHECK: ret double
function automatic real test_sqrt(real x);
    return $sqrt(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU10test_floor
// CHECK: call double @llvm.floor.f64
// CHECK: ret double
function automatic real test_floor(real x);
    return $floor(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU9test_ceil
// CHECK: call double @llvm.ceil.f64
// CHECK: ret double
function automatic real test_ceil(real x);
    return $ceil(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU8test_sin
// CHECK: call double @llvm.sin.f64
// CHECK: ret double
function automatic real test_sin(real x);
    return $sin(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU8test_cos
// CHECK: call double @llvm.cos.f64
// CHECK: ret double
function automatic real test_cos(real x);
    return $cos(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU8test_tan
// CHECK: call double @llvm.tan.f64
// CHECK: ret double
function automatic real test_tan(real x);
    return $tan(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU9test_asin
// CHECK: call double @llvm.asin.f64
// CHECK: ret double
function automatic real test_asin(real x);
    return $asin(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU9test_acos
// CHECK: call double @llvm.acos.f64
// CHECK: ret double
function automatic real test_acos(real x);
    return $acos(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU9test_atan
// CHECK: call double @llvm.atan.f64
// CHECK: ret double
function automatic real test_atan(real x);
    return $atan(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU9test_sinh
// CHECK: call double @llvm.sinh.f64
// CHECK: ret double
function automatic real test_sinh(real x);
    return $sinh(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU9test_cosh
// CHECK: call double @llvm.cosh.f64
// CHECK: ret double
function automatic real test_cosh(real x);
    return $cosh(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU9test_tanh
// CHECK: call double @llvm.tanh.f64
// CHECK: ret double
function automatic real test_tanh(real x);
    return $tanh(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU10test_atan2
// CHECK: call double @llvm.atan2.f64
// CHECK: ret double
function automatic real test_atan2(real y, real x);
    return $atan2(y, x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU8test_pow
// CHECK: call double @llvm.pow.f64
// CHECK: ret double
function automatic real test_pow(real base, real exp);
    return $pow(base, exp);
endfunction

// ============================================================
// Floating-point math — C library declarations
// ============================================================

// CHECK-LABEL: define private double @_SV0NvU10test_asinh
// CHECK: call double @asinh(
// CHECK: ret double
function automatic real test_asinh(real x);
    return $asinh(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU10test_acosh
// CHECK: call double @acosh(
// CHECK: ret double
function automatic real test_acosh(real x);
    return $acosh(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU10test_atanh
// CHECK: call double @atanh(
// CHECK: ret double
function automatic real test_atanh(real x);
    return $atanh(x);
endfunction

// CHECK-LABEL: define private double @_SV0NvU10test_hypot
// CHECK: call double @hypot(
// CHECK: ret double
function automatic real test_hypot(real x, real y);
    return $hypot(x, y);
endfunction
