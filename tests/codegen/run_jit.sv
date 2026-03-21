// Regression tests for the --run JIT flag.
// REQUIRES: llvm

// RUN: %slang --run forty_two %s
// CHECK: 42

// RUN: %slang --run neg_one %s
// CHECK: -1

// RUN: %slang --run big_unsigned %s
// CHECK: 4294967295

// RUN: %slang --run real_result %s
// CHECK: 3.14

// RUN: %slang --run loops_sum %s
// CHECK: 55

// RUN: %slang --run logic_x %s
// CHECK: 8'bxxxxxxxx

function automatic int forty_two();
    return 42;
endfunction

function automatic int neg_one();
    return -1;
endfunction

function automatic int unsigned big_unsigned();
    return 32'hFFFF_FFFF;
endfunction

function automatic shortreal real_result();
    return 3.14;
endfunction

function automatic int loops_sum();
    int s = 0;
    for (int i = 1; i <= 10; i++)
        s = s + i;
    return s;
endfunction

function automatic logic [7:0] logic_x();
    return 'x;
endfunction
