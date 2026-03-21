// Tests for 2-state bit type codegen.
// The 'bit' type is a 2-state 1-bit value, lowered to plain i1.
// REQUIRES: llvm
// RUN: %slang --emit-ir %t %s && cat %t

// CHECK-LABEL: define private i1 @bit_and
// CHECK: and i1
// CHECK: ret i1

// CHECK-LABEL: define private i1 @bit_or
// CHECK: or i1
// CHECK: ret i1

// CHECK-LABEL: define private i1 @bit_xor
// CHECK: xor i1
// CHECK: ret i1

// CHECK-LABEL: define private i8 @byte_add
// CHECK: add i8
// CHECK: ret i8

function automatic bit bit_and(bit a, bit b);
    return a & b;
endfunction

function automatic bit bit_or(bit a, bit b);
    return a | b;
endfunction

function automatic bit bit_xor(bit a, bit b);
    return a ^ b;
endfunction

function automatic byte byte_add(byte a, byte b);
    return a + b;
endfunction
