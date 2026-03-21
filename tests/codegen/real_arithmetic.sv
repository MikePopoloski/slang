// Tests for floating-point codegen (real and shortreal types).
// REQUIRES: llvm
// RUN: %slang --emit-ir - %s

// CHECK-LABEL: define private double @_SV0NvU4fadd
// CHECK: fadd double
// CHECK: ret double

// CHECK-LABEL: define private double @_SV0NvU4fsub
// CHECK: fsub double
// CHECK: ret double

// CHECK-LABEL: define private double @_SV0NvU4fmul
// CHECK: fmul double
// CHECK: ret double

// CHECK-LABEL: define private float @_SV0NvU5sfmul
// CHECK: fmul float
// CHECK: ret float

function automatic real fadd(real a, real b);
    return a + b;
endfunction

function automatic real fsub(real a, real b);
    return a - b;
endfunction

function automatic real fmul(real a, real b);
    return a * b;
endfunction

function automatic shortreal sfmul(shortreal a, shortreal b);
    return a * b;
endfunction
