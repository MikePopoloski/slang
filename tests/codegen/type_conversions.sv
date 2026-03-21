// Tests for type conversion / cast codegen.
// REQUIRES: llvm
// RUN: %slang --emit-ir %t %s && cat %t

// CHECK-LABEL: define private double @int_to_real
// CHECK: sitofp i32 {{.*}} to double
// CHECK: ret double

// CHECK-LABEL: define private i32 @real_to_int
// CHECK: fptosi double {{.*}} to i32
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
