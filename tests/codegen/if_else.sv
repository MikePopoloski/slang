// Tests for if/else control flow codegen.
// REQUIRES: llvm
// RUN: %slang --emit-ir - %s

// CHECK-LABEL: define private i32 @choose
// CHECK: br i1
// CHECK: if.then:
// CHECK: if.else:

// CHECK-LABEL: define private i32 @clamp
// CHECK: icmp slt i32
// CHECK: if.then
// CHECK: if.else
// CHECK: icmp sgt i32

function automatic int choose(int a, int b, bit sel);
    if (sel)
        return a;
    else
        return b;
endfunction

// Three-way clamp: returns lo if val < lo, hi if val > hi, else val.
function automatic int clamp(int val, int lo, int hi);
    if (val < lo)
        return lo;
    else if (val > hi)
        return hi;
    else
        return val;
endfunction
