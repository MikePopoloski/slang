// Tests for loop codegen (for, while).
// REQUIRES: llvm
// RUN: %slang --emit-ir - %s

// CHECK-LABEL: define private i32 @sum
// CHECK: for.cond:
// CHECK: icmp slt i32
// CHECK: for.body:
// CHECK: add i32
// CHECK: for.step:
// CHECK: for.exit:

// CHECK-LABEL: define private i32 @countdown
// CHECK: while.cond:
// CHECK: icmp sgt i32
// CHECK: while.body:
// CHECK: sub i32
// CHECK: while.exit:

function automatic int sum(int n);
    int s = 0;
    for (int i = 0; i < n; i = i + 1)
        s = s + i;
    return s;
endfunction

function automatic int countdown(int n);
    while (n > 0)
        n = n - 1;
    return n;
endfunction
