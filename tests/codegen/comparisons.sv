// Tests for comparison operators and boolean expressions.
// REQUIRES: llvm
// RUN: %slang --emit-ir %t %s && cat %t

// CHECK-LABEL: define private i1 @bit_lt
// CHECK: icmp ult i1
// CHECK: ret i1

// CHECK-LABEL: define private i1 @bit_eq
// CHECK: icmp eq i1
// CHECK: ret i1

// CHECK-LABEL: define private i1 @real_lt
// CHECK: fcmp olt double
// CHECK: ret i1

// CHECK-LABEL: define private i1 @real_eq
// CHECK: fcmp oeq double
// CHECK: ret i1

// Comparison of int used as a condition (not a return value).
// CHECK-LABEL: define private i32 @max_int
// CHECK: icmp sgt i32
// CHECK: br i1

function automatic bit bit_lt(bit a, bit b);
    return a < b;
endfunction

function automatic bit bit_eq(bit a, bit b);
    return a == b;
endfunction

function automatic bit real_lt(real a, real b);
    return a < b;
endfunction

function automatic bit real_eq(real a, real b);
    return a == b;
endfunction

// Comparison of int used as a condition (not a return value) works fine.
function automatic int max_int(int a, int b);
    if (a > b)
        return a;
    return b;
endfunction
