// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "AnalysisTests.h"

TEST_CASE("Class method driver crash regress GH #552") {
    auto& code = R"(
class B;
    int v[$];
endclass

class C;
    virtual function B get();
        return null;
    endfunction

    function void f();
        get().v.delete();
    endfunction
endclass
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Multiple assign to static class members") {
    auto& code = R"(
class C;
    static int foo;
endclass

function C bar;
    return null;
endfunction

module m;
    C c = new;
    assign c.foo = 1;
    assign bar().foo = 1;
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleContAssigns);
}

TEST_CASE("Multiple driver errors") {
    auto& code = R"(
module m;
    struct packed { int foo; } [1:0] bar[3];

    assign bar[0][0].foo = 1;
    assign bar[0][0].foo = 2;
    assign bar[1] = '0;

    initial begin
        bar[1][0] = '1;
        bar[2][0].foo = 1;
        bar[2][0].foo = 2;
    end

    assign bar[2][1].foo = 3;

    int i = 1;
    assign i = 2;

    wire [31:0] j = 1;
    assign j = 2;

    uwire [31:0] k = 1;
    assign k = 2;

    nettype real nt;
    nt n = 3.14;
    assign n = 2.3;
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::MultipleContAssigns);
    CHECK(diags[1].code == diag::MixedVarAssigns);
    CHECK(diags[2].code == diag::MixedVarAssigns);
    CHECK(diags[3].code == diag::MultipleUWireDrivers);
    CHECK(diags[4].code == diag::MultipleUDNTDrivers);
}

TEST_CASE("Multi-driven errors through call expressions from normal always block") {
    auto& code = R"(
module top(input clk, input reset);
    logic c;
    function logic m(logic d);
        c = d;
        return c;
    endfunction

    logic a, b;
    always_ff @(posedge clk) begin
        a <= m(a);
    end

    always @(posedge reset) begin
        b <= m(a);
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
}

// TODO: add more complicated local var test case with recursive calls
TEST_CASE("Multi-driven subroutine local var option to allow") {
    auto& code = R"(
module top(input clk, input reset);
    function logic m(logic d);
        logic c;
        c = d;
        return c;
    endfunction

    logic a, b;
    always_ff @(posedge clk) begin
        a <= m(a);
    end

    always @(posedge reset) begin
        b <= m(a);
    end
endmodule
)";

    AnalysisOptions options;
    options.flags |= AnalysisFlags::AllowMultiDrivenLocals;

    Compilation compilation;
    AnalysisManager analysisManager(options);

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("v1800-2023 clarification: multi-driven subroutine checking doesn't apply to tasks") {
    auto& code = R"(
module m;
    int i;
    task t;
        i <= 1;
    endtask

    always_comb t();
    always_comb t();
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Recursive function in always_comb driver check") {
    auto& code = R"(
module top;
  logic passed;
  logic [7:0] value;
  integer ones;

  function automatic integer count_by_one(input integer start);
    if (start != 0) count_by_one = (value[start] ? 1 : 0) + count_ones(start-1);
    else count_by_one = value[start] ? 1 : 0;
  endfunction

  function automatic integer count_ones(input integer start);
    if (start != 0) count_ones = (value[start] ? 1 : 0) + count_by_one(start-1);
    else count_ones = value[start] ? 1 : 0;
  endfunction

  always_comb ones = count_ones(7);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Proc subroutine multiple driver tracking") {
    auto& code = R"(
module m;
    logic [9:0] a;
    always_comb begin
        for (int i = 0; i < $size(a); i++)
            a[i] = 0;
        baz();
        baz();
    end

    task baz;
        a[0] = 1;
    endtask
endmodule
)";

    // This tests a crash due to invalidating iterators while
    // iterating the variable's driver map.
    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Multi-driven unpacked array regress GH #923") {
    auto& code = R"(
// Range select in unpacked array, causing error.
module Test1;
  parameter DIM1 = 2;
  parameter DIM2 = 4;

  logic test [DIM1-1:0][DIM2-1:0];

  // i == 2, elemRange = {1, 1}, start 1, width 1, elemWidth 4, result = {4, 7}
  // i == 1, elemRange = {1, 3}, start 1, width 3, elemWidth 3, result = {7, 9}, should be {5, 7}
  assign test[0][DIM2-2:0] = '{default: '0};

  // i == 2, elemRange = {1, 1}, start 1, width 1, elemWidth 4, result = {4, 7}
  // i == 1, elemRange = {0, 0}, start 0, width 1, elemWidth 1, result = {4, 4}
  assign test[0][DIM2-1]   = '0;

  // i == 2, elemRange = {0, 0}, start 0, width 1, elemWidth 4, result = {0, 3}
  // i == 1, elemRange = {1, 3}, start 1, width 3, elemWidth 3, result = {3, 5}, should be {1, 3}
  assign test[1][DIM2-2:0] = '{default: '0};

  // i == 2, elemRange = {0, 0}, start 0, width 1, elemWidth 4, result = {0, 3}
  // i == 1, elemRange = {0, 0}, start 0, width 1, elemWidth 1, result = {0, 0}
  assign test[1][DIM2-1]   = '0;

endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Invalid selection driver bounds regress -- GH #1141") {
    auto& code = R"(
module test;
  reg [15:0] vect;

  initial begin
    vect[1 -: 4] = 8'b1010_1010;
  end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Modport multi-driven errors") {
    auto& code = R"(
interface I;
    int i;
    modport m(output i);
endinterface

module m(I.m i);
    assign i.i = 1;
endmodule

interface J;
    logic [3:0] a;
    logic [2:0] b;
    modport m(output .R(b[1:0]));
endinterface

module n(J.m j);
    assign j.R[1:0] = 2;
endmodule

module top;
    I i();
    m m1(i), m2(i);

    J j1(), j2();
    n n1(j1), n2(j2);

    assign j2.b[1] = 1;
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::MultipleContAssigns);
    CHECK(diags[1].code == diag::MultipleContAssigns);
}

TEST_CASE("Iface connection multi-driven through array errors") {
    auto& code = R"(
interface I;
    for (genvar i = 0; i < 5; i++) begin : asdf
        logic a;
    end
endinterface

interface J;
    I i[3] ();
    logic q;
    modport m(input q);
endinterface

module m(I i);
    assign i.asdf[4].a = 1;
endmodule

module n(I i[3]);
    assign i[2].asdf[4].a = 1;
endmodule

module o(J j);
    assign j.i[1].asdf[2].a = 1;
endmodule

module top;
    I i();
    m m1(i), m2(i);

    I arr [3] ();
    n n1(arr), n2(arr);

    J j();
    o o1(j.m), o2(j.m);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::MultipleContAssigns);
    CHECK(diags[1].code == diag::MultipleContAssigns);
    CHECK(diags[2].code == diag::MultipleContAssigns);
}

TEST_CASE("Interface array multi-driven error regress") {
    auto& code = R"(
interface I;
    int i;
    modport m(output i);
endinterface

module mod(I.m arr[3]);
    for (genvar i = 0; i < 3; i++) begin
        always_comb arr[i].i = i;
    end
endmodule

module top;
    I i [3]();
    mod m1(i);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Multiple layers of interface ports and cache interaction") {
    auto& code = R"(
interface I;
    logic l;
endinterface

module m(I i);
    assign i.l = 1;
endmodule

module n(I i[2]);
    m m1(i[1]);
endmodule

module o(I i[3]);
    n n1(i[1:2]);
endmodule

module top;
    I i [3]();
    o o1(i), o2(i);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleContAssigns);
}

TEST_CASE("always_comb drivers within nested functions") {
    auto& code = R"(
module m;
    int baz;

    function void f1(int bar);
      baz = bar;
    endfunction

    function void f2(int bar);
      f1(bar);
    endfunction

    always_comb f2(2);
    always_comb f2(3);

    int v;
    function void f3(int bar);
      v = bar;
    endfunction

    always_comb f3(4);

    int foo;
    task t;
      foo <= 1;
    endtask

    always_comb begin
      foo <= 2;
      t();
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("always_comb dup driver with initial block with language option") {
    auto& code = R"(
module m;
    int foo[2];

    initial begin
        for (int i = 0; i < 2; i++)
            foo[i] = 0;
    end

    always_comb foo[1] = 1;
endmodule
)";

    AnalysisOptions options;
    options.flags |= AnalysisFlags::AllowDupInitialDrivers;

    Compilation compilation;
    AnalysisManager analysisManager(options);

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("hierarchical driver errors") {
    auto& code = R"(
interface I;
    int foo;
endinterface

module m;
    I i();

    n n1(i);
    n n2(i);
endmodule

module n(I i);
    always_comb i.foo = 1;
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);

    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:14:17: error: variable 'foo' driven by always_comb procedure cannot be written to by any other process
    always_comb i.foo = 1;
                ^~~~~
note: from 'm.n2' and 'm.n1'
)");
}

TEST_CASE("lvalue driver assertion regression GH #551") {
    auto& code = R"(
module M #(parameter int W=1) (
    input  logic         clk,
    input  logic         rst,
    input  logic [W-1:0] d,
    output logic [W-1:0] o
);
endmodule

module M2 #(
    parameter int W = 2
) (
    input logic clk,
    input logic rst
);
    localparam int W_MAX = $clog2(W);

    logic [W_MAX:0] d, o;
    logic x_d, x_o;

    M m [W_MAX+1:0] (
        .clk (clk),
        .rst (rst),
        .d   ({x_d, d}),
        .o   ({x_o, o})
    );
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Unrollable for loop drivers") {
    auto& code = R"(
 module m;
    int foo[10];
    initial
        for (int i = 1; i < 10; i += 2) begin : baz
            foo[i] = 2;
        end

    for (genvar i = 0; i < 10; i += 2) begin
        always_comb foo[i] = 1;
    end

    always_comb foo[1] = 1; // error

    struct { int foo; int bar; } baz[3][2];
    initial begin
        while (1) begin
            for (int i = 0; i < 3; i++) begin
                for (int j = 0; j < 2; j++) begin
                    forever begin
                        if (i != 2 || j != 1)
                            #1 baz[i][j].foo = 1;
                        break;
                    end
                end
            end
        end
    end
    for (genvar i = 0; i < 3; i++) begin
        always_comb baz[i][0].bar = 3;
    end

    always_comb baz[1][1].foo = 4; // error
    always_comb baz[1][1].bar = 4;
    always_comb baz[2][1].foo = 3;

    struct { int foo; int bar; } arr[21474836];
    initial begin
        for (int i = 0; i < 2147483647; i++) begin
            arr[i].foo = 1;
        end
    end
    always_comb arr[0].bar = 2;
 endmodule
)";

    AnalysisOptions options;
    options.maxLoopAnalysisSteps = 8192;

    Compilation compilation;
    AnalysisManager analysisManager(options);

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[1].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[2].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("Unrollable for loop drivers -- strict checking") {
    auto& code = R"(
module m;
    int foo[10];
    initial
        for (int i = 1; i < 10; i += 2) begin : baz
            foo[i] = 2;
        end

    for (genvar i = 0; i < 10; i += 2) begin
        always_comb foo[i] = 1;
    end
endmodule
)";

    AnalysisOptions options;
    options.maxLoopAnalysisSteps = 0;

    Compilation compilation;
    AnalysisManager analysisManager(options);

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("driver checking applied to subroutine ref args") {
    auto& code = R"(
function automatic void f(ref int a);
endfunction

function automatic void g(const ref int a);
endfunction

module m;
    int i;
    always_comb begin
        f(i);
        g(i);
    end
    always_comb begin
        f(i);
        g(i);
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("Function arg defaults with multi-driver checking") {
    auto& code = R"(
int baz, bar, biz;

function automatic void f1(output int a = baz, ref int b = bar);
endfunction

function automatic void f2(inout int c = biz);
endfunction

module m;
    initial f1();
    always_comb begin
        f1();
    end

    assign biz = 1;
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[1].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("Instance caching with $root scope upward names") {
    auto& code = R"(
module m;
    assign $root.top.n1.l = 1;
endmodule

module n;
    logic l;
endmodule

module top;
    n n1();
    m m1(), m2();
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleContAssigns);
}

TEST_CASE("Instance caching with downward names") {
    auto& code = R"(
module m;
    logic i;
    assign i = 0;
endmodule

module top;
    assign m2.i = 1;
    m m1(), m2();
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleContAssigns);
}

TEST_CASE("Multiple always assigns") {
    auto& code = R"(
module m;
    logic [2:0] a;
    int b = 1;
    int c;
    always_comb begin : boz
        a[0] = 1;
        a[1:0] = 2;
        b = 3;
        c = 1;
    end

    wire clk;
    always_ff @(posedge clk) begin : baz
        a[1] <= 1;
    end

    always_latch begin : foo
        b = 4;
    end

    always @* c = 3;

    int l = 1;
    always_ff @(posedge clk) begin
        l <= 2;
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[1].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[2].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("UDNT resolution func driven arg") {
    auto& code = R"(
module m;
    nettype real nt11 with func8;

    function real func8(real r[]);
        r[1] = 3.14;
        return r[1];
    endfunction
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto [diags, design] = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NTResolveArgModify);
}
