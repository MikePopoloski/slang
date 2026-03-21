// Tests for 2-state integer arithmetic codegen.
// REQUIRES: llvm
// RUN: %slang --emit-ir - %s

// CHECK-LABEL: define private i32 @_SV0NvU3add
// CHECK: %a = alloca i32
// CHECK: %b = alloca i32
// CHECK: add i32
// CHECK: ret i32

// CHECK-LABEL: define private i32 @_SV0NvU3sub
// CHECK: sub i32
// CHECK: ret i32

// CHECK-LABEL: define private i32 @_SV0NvU3mul
// CHECK: mul i32
// CHECK: ret i32

// CHECK-LABEL: define private i32 @_SV0NvU6negate
// CHECK: sub i32 0,
// CHECK: ret i32

function automatic int add(int a, int b);
    return a + b;
endfunction

function automatic int sub(int a, int b);
    return a - b;
endfunction

function automatic int mul(int a, int b);
    return a * b;
endfunction

function automatic int negate(int a);
    return -a;
endfunction
