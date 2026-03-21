// Tests for function call codegen (cross-function calls).
// REQUIRES: llvm
// RUN: %slang --emit-ir %t %s && cat %t

// CHECK-LABEL: define private i32 @double_it
// CHECK: mul i32
// CHECK: ret i32

// CHECK-LABEL: define private i32 @quad
// CHECK: call i32 @double_it
// CHECK: call i32 @double_it
// CHECK: ret i32

// CHECK-LABEL: define private i32 @accumulate
// CHECK: %a = alloca i32
// CHECK: %b = alloca i32
// CHECK: %c = alloca i32
// CHECK: %tmp = alloca i32
// CHECK: add i32
// CHECK: store i32
// CHECK: add i32
// CHECK: ret i32

function automatic int double_it(int x);
    return x * 2;
endfunction

// Calls double_it twice: effectively multiplies by 4.
function automatic int quad(int x);
    return double_it(double_it(x));
endfunction

// Uses a named local variable as an intermediate.
function automatic int accumulate(int a, int b, int c);
    int tmp = 0;
    tmp = a + b;
    return tmp + c;
endfunction
