// Tests for constant / literal codegen.
// REQUIRES: llvm
// RUN: %slang --emit-ir - %s

// CHECK-LABEL: define private i32 @_SV0NvU8const_42
// CHECK: store i32 42

// CHECK-LABEL: define private i32 @_SV0NvU10const_zero
// CHECK: store i32 0

// CHECK-LABEL: define private i32 @_SV0NvU9const_neg
// CHECK: store i32 -1

// CHECK-LABEL: define private double @_SV0NvU8const_pi
// CHECK: store double 0x400921FB54442D11

// CHECK-LABEL: define private i1 @_SV0NvU10const_true
// CHECK: store i1 true

function automatic int const_42();
    return 42;
endfunction

function automatic int const_zero();
    return 0;
endfunction

function automatic int const_neg();
    return -1;
endfunction

function automatic real const_pi();
    return 3.14159265358979;
endfunction

function automatic bit const_true();
    return 1'b1;
endfunction
