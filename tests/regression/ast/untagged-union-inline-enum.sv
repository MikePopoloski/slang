// SPDX-License-Identifier: MIT

// RUN: %slang %s -j1

module m;
    typedef struct { int value; } payload_t;
    typedef union { enum logic [1:0] { E0, E1 } marker; payload_t a; payload_t b; } u_t;
    function automatic int f();
        u_t u;
        u.a.value = 5;
        return u.b.value;
    endfunction
    localparam int X = f();
    function automatic int check(int value);
        if (value != 5)
            $fatal(1, "inactive union field has unexpected value");
        return value;
    endfunction
    localparam int Checked = check(X);
endmodule
