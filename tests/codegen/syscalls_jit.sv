// JIT execution tests for built-in system call codegen.
// Tests that e.g. $rtoi, $itor, $clog2, $floor, $ceil, and bit-pattern conversions
// produce the expected results at runtime.
// REQUIRES: llvm

// RUN: %slang --run rtoi_trunc %s
// CHECK: 3

// RUN: %slang --run itor_val %s
// CHECK: 42

// RUN: %slang --run clog2_zero %s
// CHECK: 0

// RUN: %slang --run clog2_one %s
// CHECK: 0

// RUN: %slang --run clog2_eight %s
// CHECK: 3

// RUN: %slang --run clog2_nine %s
// CHECK: 4

// RUN: %slang --run floor_val %s
// CHECK: 2

// RUN: %slang --run ceil_val %s
// CHECK: 3

// RUN: %slang --run bits_roundtrip %s
// CHECK: 1

// RUN: %slang --run shortreal_bits_roundtrip %s
// CHECK: 1

// $rtoi truncates toward zero.
function automatic int rtoi_trunc();
    return $rtoi(3.9);
endfunction

// $itor followed by $rtoi round-trips.
function automatic int itor_val();
    real r = $itor(42);
    return $rtoi(r);
endfunction

// $clog2(0) == 0
function automatic int clog2_zero();
    return $clog2(0);
endfunction

// $clog2(1) == 0
function automatic int clog2_one();
    return $clog2(1);
endfunction

// $clog2(8) == 3  (exact power of two)
function automatic int clog2_eight();
    return $clog2(8);
endfunction

// $clog2(9) == 4  (one above a power of two)
function automatic int clog2_nine();
    return $clog2(9);
endfunction

// $floor(2.7) == 2.0
function automatic int floor_val();
    return $rtoi($floor(2.7));
endfunction

// $ceil(2.3) == 3.0
function automatic int ceil_val();
    return $rtoi($ceil(2.3));
endfunction

// $realtobits / $bitstoreal round-trip should be lossless.
function automatic int bits_roundtrip();
    real x = 1.5;
    real y = $bitstoreal($realtobits(x));
    return (x == y) ? 1 : 0;
endfunction

// $shortrealtobits / $bitstoshortreal round-trip.
function automatic int shortreal_bits_roundtrip();
    shortreal x = 1.5;
    shortreal y = $bitstoshortreal($shortrealtobits(x));
    return (x == y) ? 1 : 0;
endfunction
