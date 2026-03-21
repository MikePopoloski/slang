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
// CHECK: 1'bx

// RUN: %slang "--run=add_ints(3, 4)" %s
// CHECK: 7

// RUN: %slang "--run=negate(99)" %s
// CHECK: -99

// RUN: %slang "--run=negate(-5)" %s
// CHECK: 5

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

function automatic logic logic_x();
    return 'x;
endfunction

function automatic int add_ints(int a, int b);
    return a + b;
endfunction

function automatic int negate(int x);
    return -x;
endfunction
