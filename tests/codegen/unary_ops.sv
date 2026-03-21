// Regression tests for unary operator codegen.
// 2-state (bit/int) types are lowered to plain iN integers.
// 4-state (logic) types are lowered to i(2N): low N bits = value, high N bits = unknown mask.
// REQUIRES: llvm
// RUN: %slang --emit-ir - %s

// ============================================================
// 2-state unary operators on bit [7:0]
// ============================================================

// CHECK-LABEL: define private i8 @bit8_plus
// CHECK: ret i8
function automatic bit [7:0] bit8_plus(bit [7:0] a);
    return +a;
endfunction

// CHECK-LABEL: define private i8 @bit8_minus
// CHECK: sub i8 0,
// CHECK: ret i8
function automatic bit [7:0] bit8_minus(bit [7:0] a);
    return -a;
endfunction

// CHECK-LABEL: define private i8 @bit8_bitnot
// CHECK: xor i8
// CHECK: ret i8
function automatic bit [7:0] bit8_bitnot(bit [7:0] a);
    return ~a;
endfunction

// CHECK-LABEL: define private i1 @bit8_lognot
// CHECK: icmp ne i8
// CHECK: ret i1
function automatic bit bit8_lognot(bit [7:0] a);
    return !a;
endfunction

// CHECK-LABEL: define private i1 @bit8_reduce_and
// CHECK: icmp eq i8
// CHECK: ret i1
function automatic bit bit8_reduce_and(bit [7:0] a);
    return &a;
endfunction

// CHECK-LABEL: define private i1 @bit8_reduce_nand
// CHECK: icmp ne i8
// CHECK: ret i1
function automatic bit bit8_reduce_nand(bit [7:0] a);
    return ~&a;
endfunction

// CHECK-LABEL: define private i1 @bit8_reduce_or
// CHECK: icmp ne i8
// CHECK: ret i1
function automatic bit bit8_reduce_or(bit [7:0] a);
    return |a;
endfunction

// CHECK-LABEL: define private i1 @bit8_reduce_nor
// CHECK: icmp eq i8
// CHECK: ret i1
function automatic bit bit8_reduce_nor(bit [7:0] a);
    return ~|a;
endfunction

// CHECK-LABEL: define private i1 @bit8_reduce_xor
// CHECK: call i8 @llvm.ctpop.i8
// CHECK: icmp ne i8
// CHECK: ret i1
function automatic bit bit8_reduce_xor(bit [7:0] a);
    return ^a;
endfunction

// CHECK-LABEL: define private i1 @bit8_reduce_xnor
// CHECK: call i8 @llvm.ctpop.i8
// CHECK: ret i1
function automatic bit bit8_reduce_xnor(bit [7:0] a);
    return ~^a;
endfunction

// ============================================================
// 2-state unary operators on int (i32)
// ============================================================

// CHECK-LABEL: define private i32 @int_plus
// CHECK: ret i32
function automatic int int_plus(int a);
    return +a;
endfunction

// CHECK-LABEL: define private i32 @int_minus
// CHECK: sub i32 0,
// CHECK: ret i32
function automatic int int_minus(int a);
    return -a;
endfunction

// CHECK-LABEL: define private i32 @int_bitnot
// CHECK: xor i32
// CHECK: ret i32
function automatic int int_bitnot(int a);
    return ~a;
endfunction

// CHECK-LABEL: define private i1 @int_lognot
// CHECK: icmp ne i32
// CHECK: ret i1
function automatic bit int_lognot(int a);
    return !a;
endfunction

// ============================================================
// 4-state unary operators on logic [7:0] -> result is i16
// ============================================================

// CHECK-LABEL: define private i16 @logic8_plus
// CHECK: ret i16
function automatic logic [7:0] logic8_plus(logic [7:0] a);
    return +a;
endfunction

// CHECK-LABEL: define private i16 @logic8_minus
// CHECK: icmp ne i8
// CHECK: select i1
// CHECK: ret i16
function automatic logic [7:0] logic8_minus(logic [7:0] a);
    return -a;
endfunction

// CHECK-LABEL: define private i16 @logic8_bitnot
// CHECK: xor i8
// CHECK: ret i16
function automatic logic [7:0] logic8_bitnot(logic [7:0] a);
    return ~a;
endfunction

// Result of ! on logic [7:0] is logic (1 bit) -> i2
// CHECK-LABEL: define private i2 @logic8_lognot
// CHECK: icmp ne i8
// CHECK: icmp eq i8
// CHECK: ret i2
function automatic logic logic8_lognot(logic [7:0] a);
    return !a;
endfunction

// CHECK-LABEL: define private i2 @logic8_reduce_and
// CHECK: icmp ne i8
// CHECK: or i8
// CHECK: icmp eq i8
// CHECK: ret i2
function automatic logic logic8_reduce_and(logic [7:0] a);
    return &a;
endfunction

// CHECK-LABEL: define private i2 @logic8_reduce_nand
// CHECK: icmp ne i8
// CHECK: or i8
// CHECK: icmp eq i8
// CHECK: ret i2
function automatic logic logic8_reduce_nand(logic [7:0] a);
    return ~&a;
endfunction

// CHECK-LABEL: define private i2 @logic8_reduce_or
// CHECK: icmp ne i8
// CHECK: icmp ne i8
// CHECK: ret i2
function automatic logic logic8_reduce_or(logic [7:0] a);
    return |a;
endfunction

// CHECK-LABEL: define private i2 @logic8_reduce_nor
// CHECK: icmp ne i8
// CHECK: icmp ne i8
// CHECK: ret i2
function automatic logic logic8_reduce_nor(logic [7:0] a);
    return ~|a;
endfunction

// CHECK-LABEL: define private i2 @logic8_reduce_xor
// CHECK: icmp ne i8
// CHECK: call i8 @llvm.ctpop.i8
// CHECK: icmp ne i8
// CHECK: ret i2
function automatic logic logic8_reduce_xor(logic [7:0] a);
    return ^a;
endfunction

// CHECK-LABEL: define private i2 @logic8_reduce_xnor
// CHECK: icmp ne i8
// CHECK: call i8 @llvm.ctpop.i8
// CHECK: icmp ne i8
// CHECK: ret i2
function automatic logic logic8_reduce_xnor(logic [7:0] a);
    return ~^a;
endfunction

// ============================================================
// 4-state unary operators on logic (1 bit) -> result is i2
// ============================================================

// CHECK-LABEL: define private i2 @logic1_lognot
// CHECK: ret i2
function automatic logic logic1_lognot(logic a);
    return !a;
endfunction

// CHECK-LABEL: define private i2 @logic1_reduce_and
// CHECK: ret i2
function automatic logic logic1_reduce_and(logic a);
    return &a;
endfunction

// CHECK-LABEL: define private i2 @logic1_reduce_or
// CHECK: ret i2
function automatic logic logic1_reduce_or(logic a);
    return |a;
endfunction

// CHECK-LABEL: define private i2 @logic1_reduce_xor
// CHECK: ret i2
function automatic logic logic1_reduce_xor(logic a);
    return ^a;
endfunction

// RUN: %slang --run real_preinc %s
// CHECK: 2.3
function automatic real real_preinc();
    real r = 1.3;
    return ++r;
endfunction

// RUN: %slang --run real_postinc %s
// CHECK: 1.3
function automatic real real_postinc();
    real r = 1.3;
    return r++;
endfunction

// RUN: %slang --run shortreal_preinc %s
// CHECK: 2.3
function automatic shortreal shortreal_preinc();
    shortreal r = 1.3;
    return ++r;
endfunction

// RUN: %slang --run shortreal_postinc %s
// CHECK: 1.3
function automatic shortreal shortreal_postinc();
    shortreal r = 1.3;
    return r++;
endfunction

// RUN: %slang --run bit_preinc %s
// CHECK: 9
function automatic bit[7:0] bit_preinc();
    bit [7:0] b = 8;
    return ++b;
endfunction

// RUN: %slang --run bit_postinc %s
// CHECK: 8
function automatic bit[7:0] bit_postinc();
    bit [7:0] b = 8;
    return b++;
endfunction

// RUN: %slang --run logic_preinc %s
// CHECK: 9
function automatic logic[7:0] logic_preinc();
    logic [7:0] l = 8;
    return ++l;
endfunction

// RUN: %slang --run logic_postinc %s
// CHECK: 8
function automatic logic[7:0] logic_postinc();
    logic [7:0] l = 8;
    return l++;
endfunction

// RUN: %slang --run logic_unk_preinc %s
// CHECK: 8'bxxxxxxxx
function automatic logic[7:0] logic_unk_preinc();
    logic [7:0] l = 8'b101z1001;
    return ++l;
endfunction

// RUN: %slang --run logic_unk_postinc %s
// CHECK: 8'b101z1001
function automatic logic[7:0] logic_unk_postinc();
    logic [7:0] l = 8'b101z1001;
    return l++;
endfunction
