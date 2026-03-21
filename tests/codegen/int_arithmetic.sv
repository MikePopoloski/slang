// Tests for 2-state integer arithmetic codegen.
// REQUIRES: llvm
// RUN: %slang --emit-ir - %s

// CHECK-LABEL: define private i32 @add
// CHECK: %a = alloca i32
// CHECK: %b = alloca i32
// CHECK: add i32
// CHECK: ret i32

// CHECK-LABEL: define private i32 @sub
// CHECK: sub i32
// CHECK: ret i32

// CHECK-LABEL: define private i32 @mul
// CHECK: mul i32
// CHECK: ret i32

// CHECK-LABEL: define private i32 @negate
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
