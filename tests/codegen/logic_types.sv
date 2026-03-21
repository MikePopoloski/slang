// Tests for 4-state logic type codegen.
// 4-state types are lowered to { iN, iN } structs where the first field
// holds the value bits and the second holds the unknown ("X") mask.
// REQUIRES: llvm
// RUN: %slang --emit-ir - %s

// CHECK-LABEL: define private i2 @_SV0NvU10logic1_and
// CHECK: ret i2

// CHECK-LABEL: define private i16 @_SV0NvU10logic8_and
// CHECK: ret i16

// CHECK-LABEL: define private i16 @_SV0NvU9logic8_or
// CHECK: ret i16

// CHECK-LABEL: define private i16 @_SV0NvU10logic8_xor
// CHECK: ret i16

function automatic logic logic1_and(logic a, logic b);
    return a & b;
endfunction

function automatic logic [7:0] logic8_and(logic [7:0] a, logic [7:0] b);
    return a & b;
endfunction

function automatic logic [7:0] logic8_or(logic [7:0] a, logic [7:0] b);
    return a | b;
endfunction

function automatic logic [7:0] logic8_xor(logic [7:0] a, logic [7:0] b);
    return a ^ b;
endfunction
