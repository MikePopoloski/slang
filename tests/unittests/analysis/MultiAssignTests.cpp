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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
}

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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);

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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
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
        if (b)
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

    auto diags = analyze(code, compilation, analysisManager);
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

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::NTResolveArgModify);
}

TEST_CASE("Assigning to input ports") {
    auto& code = R"(
module m(input .a(a), input int b, output int c);
    int a;
    assign a = 1;
    assign b = 2;
endmodule

module n(a[1:0]);
    input var [3:0] a;
    assign a[2:1] = 1;
    assign a[3] = 1;
endmodule

module o;
    int a, b, c = 1;
    m m1(.a, .b, .c);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::InputPortAssign);
    CHECK(diags[1].code == diag::InputPortAssign);
    CHECK(diags[2].code == diag::InputPortAssign);
    CHECK(diags[3].code == diag::MixedVarAssigns);
}

TEST_CASE("Net port coercion") {
    auto& code = R"(
module top;
    wire in1, out1;
    m m(in1, out1);
    assign out1 = 1'b1;
endmodule

module m (in1, out1);
    input in1;
    output out1;        // out1 is driven outside the module and thus used as an input
    assign in1 = 1'b0 ; // in1 is driven within the module and thus used as an output
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::OutputPortCoercion);
    CHECK(diags[1].code == diag::InputPortCoercion);
}

TEST_CASE("Assigning to output clock var") {
    auto& code = R"(
module m(input clk);
    int j;
    assign j = 1;
    clocking cb2 @clk;
        output j;
    endclocking
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ClockVarTargetAssign);
}

TEST_CASE("Assign to invalid mod instance in interface instance") {
    auto& code = R"(
module m;
    int i;
endmodule

interface I;
    m m1();
endinterface

module n(I i);
    assign i.m1.i = 1;
endmodule

module top;
    m m1();

    I i();
    n n1(i);

    I i2();
    n n2(i2);
endmodule
)";

    // The code here is invalid because module instances are not allowed in
    // interfaces, but we want to make sure we don't crash in the analysis
    // manager when analyzing this code.
    Compilation compilation;
    AnalysisManager analysisManager;

    auto tree = SyntaxTree::fromText(code);
    compilation.addSyntaxTree(tree);
    compilation.getAllDiagnostics();
    compilation.freeze();

    analysisManager.analyze(compilation);
    auto diags = analysisManager.getDiagnostics();

    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Assigning to modport through modport") {
    auto& code = R"(
interface I;
    int i;
    modport m(output i);
endinterface

interface J(I.m m);
    modport n(output .q(m.i));
endinterface

module m(J.n n);
    assign n.q = 1;
endmodule

module top;
    I i1();
    J j1(i1);
    m m1(j1);
    m m2(j1);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleContAssigns);
}

TEST_CASE("Multi assign with procedural assign / force, events") {
    auto& code = R"(
module m;
  logic [1:0] a;
  logic [1:0] b;
  logic [1:0] c;

  initial begin
    deassign a;
    assign b = 2;
    force c = 3;
    release c;
  end

  assign a[0] = 1;
  always_comb a[1] = 1;
  always_comb b = 2;
  always_comb c = 3;

  event e;
  always_comb -> e;
  always_comb ->> e;
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("Multi assign from various syscalls") {
    auto& code = R"(
module m;
    int a;
    assign a = 1;

    always_comb std::randomize(a);

    int arr[int];
    always_comb arr.first(a);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::MixedVarAssigns);
    CHECK(diags[1].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("Multi assign from non-procedural contexts") {
    auto& code = R"(
module n(input k);
endmodule

primitive p(output a, input b, input c);
    table
        0 0 : 0;
        1 1 : 1;
    endtable
endprimitive

module m;
    int i, j, k, l;
    function f1;
        i = 1;
        return i;
    endfunction

    function f2;
        j = 1;
        return j;
    endfunction

    function f3;
        k = 1;
        return k;
    endfunction

    always_comb begin
        i = 1;
        j = 2;
        k = 3;
        l = 4;
    end

    logic r;
    assign r = f1();
    wire s = f2();

    checker c(output int o);
    endchecker

    c c1(r);
    initial c c2(r);

    n n1(f3());

    p p1(l, 0, 1);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[1].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[2].code == diag::MultipleAlwaysAssigns);
    CHECK(diags[3].code == diag::MultipleContAssigns);
    CHECK(diags[4].code == diag::MultipleContAssigns);
    CHECK(diags[5].code == diag::MixedVarAssigns);
}

TEST_CASE("Multi assign via mutually referential interfaces") {
    auto& code = R"(
interface I;
    int q;
    J j(m.i);

    modport m(output q);
endinterface

interface J(I.m i);
    assign i.j.i.j.i.q = 1;
endinterface

module m;
    I i();
    J j(i);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleContAssigns);
}

TEST_CASE("Multi assign loop analysis regress -- GH #1454") {
    auto& code = R"(
module top #(
    parameter int unsigned P  = 4
);
    localparam C = 1;

    typedef struct packed {
        logic a;
        logic b;
    } type1;

    type1 [P-1:0][C-1:0] t1;

    typedef struct packed {
        logic a;
    } type2;

    type2 [P-1:0][C-1:0] t2_a, t2_b;

    always_comb begin
        for (int unsigned p=0; p<P; p++) begin
            for (int unsigned c=0; c<C; c++) begin
                t1[p][c].a = '0;
            end
        end
    end

    always_comb begin
        for (int unsigned p=0; p<P; p++) begin
            for (int unsigned c=0; c<C; c++ ) begin
                t1[p][c].b = '0;
            end

            for (int unsigned c=0; c<C; c++ ) begin
                t2_a[p][c].a = 1'b0;
            end

            for (int unsigned c=0; c<C; c++) begin
                if (~t2_b[p][c].a) begin
                end
            end

            for (int unsigned c=0; c<C; c++) begin
                for (int unsigned c=0; c<C; c++) begin
                    t1[p][c].b = '1;
                end
            end
        end
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Multi assign through ref ports") {
    auto& code = R"(
module m(ref int r);
endmodule

module n(ref int s);
    assign s = 2;
endmodule

module top1;
    int r, s;
    m m1(r);
    n n1(s);

    assign r = 3;
    assign s = 1;
endmodule

module o(ref int s);
    q q1(s);
endmodule

module p(ref int s);
    o o1(s);
endmodule

module top2;
    int r;
    p p1(r);
    p p2(r);
endmodule

module q(ref int t);
    assign t = 2;
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::MultipleContAssigns);
    CHECK(diags[1].code == diag::MultipleContAssigns);
}

TEST_CASE("Multi assign through ref ports 2") {
    auto& code = R"(
module r({a, b});
    ref logic a;
    output logic b;
    assign a = 1;
endmodule

module v(ref .a(foo.b));
    struct { logic a; logic b; } foo;
    assign foo.b = 1;
endmodule

module w(ref .a(foo[0][1]));
    logic [1:0] foo[2][3];
    assign foo[0][1][0] = 1;
    assign foo[0][1][1] = 1;

    assign foo[1][0] = 1;
    assign foo[1][0][1] = 1;
endmodule

module x(ref .a(foo), .b(foo));
    logic foo;
    assign foo = 1;
endmodule

module y(ref .a(foo[0]));
    logic [5:3] foo[2];
    assign foo[0][5] = 1;
endmodule

module top;
    logic [1:0] q;
    r r1(q);
    assign q[1] = 1;

    logic s [1:0][3:1];
    v v1(s[1][1]);
    assign s[1][1] = 1;

    logic [1:0] t [1:0][3:1];
    w w1(t[1][1]);
    assign t[1][1][0] = 1;

    logic u, v;
    x x1(u, v);
    assign {u, v} = 1;

    logic [2:4] z;
    y y1(z);
    assign z[2:3] = 1;
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::MultipleContAssigns);
    CHECK(diags[1].code == diag::MultipleContAssigns);
    CHECK(diags[2].code == diag::MultipleContAssigns);
    CHECK(diags[3].code == diag::MultipleContAssigns);
    CHECK(diags[4].code == diag::MultipleContAssigns);
    CHECK(diags[5].code == diag::MultipleContAssigns);
}

TEST_CASE("Multi assign through ref ports 3") {
    auto& code = R"(
module y(ref .a(foo));
    logic [5:3] foo;
    assign foo[3] = 1;
endmodule

module b(ref logic[7:0] a [2:6]);
    assign a[3][5:4] = 1;
endmodule

typedef struct { logic a[2:8]; } bar_t;
module c(ref bar_t a);
    assign a.a[4:5] = '{1, 0};
endmodule

module top;
    logic [2:4] z;
    y y1(z);
    assign z[4] = 1;

    struct packed { logic a; logic b; } [1:4] a [5:1];
    b b1(a);
    assign a[4][2].b = 1;

    bar_t d;
    c c1(d);
    assign d.a[4:5] = '{0, 1};
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::MultipleContAssigns);
    CHECK(diags[1].code == diag::MultipleContAssigns);
    CHECK(diags[2].code == diag::MultipleContAssigns);
}

TEST_CASE("Multi assign through ref ports 4") {
    auto& code = R"(
module m(a);
    ref a;
    logic [3:0] a;

    always_comb a[3] = 1;

    always_comb begin
        for (int i = 0; i < 4; i++)
            a[i] = 1;
    end
endmodule

module top;
    logic [3:0] a;
    m m1(a);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("Multi assign complicated modport expressions") {
    auto& code = R"(
class C;
    int i;
endclass

interface I;
    logic [1:0] b, d;
    logic [2:3] c, e;
    C g;

    typedef struct { logic [1:0] q; logic [1:0] r; } S;

    modport m(output .a({b, c}), .d(S'{d, e}), .f(g), ref .h(g));
endinterface

module n(I.m im);
    C c = new;
    assign im.a[2] = 1;
    assign im.d.r[0] = 1;
    always_comb im.f = c;
    always_comb im.h = c;
endmodule

module top;
    I i();
    n n1(i);

    assign i.b[0] = 1;
    assign i.d = 1;
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::MultipleContAssigns);
    CHECK(diags[1].code == diag::MultipleContAssigns);
    CHECK(diags[2].code == diag::MultipleAlwaysAssigns);
}

TEST_CASE("For loop unrolling diagnostic preserves select info") {
    auto& code = R"(
module m;
    logic [3:0] a;
    always_comb a[2] = 1;
    always_comb begin
        for (int i = 0; i < 3; i++)
            a[i] = 1;
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);

    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:7:13: error: variable 'a[2]' driven by always_comb procedure cannot be written to by any other process
            a[i] = 1;
            ^~~~
source:4:17: note: also assigned here
    always_comb a[2] = 1;
                ^~~~
)");
}

TEST_CASE("Multi-ports with output segments register drivers correctly") {
    auto& code = R"(
module m({a, b});
    input a;
    output b;
endmodule

module top;
    logic [1:0] a;
    m m1(a);

    assign a[0] = 1;
    assign a[1] = 1;
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultipleContAssigns);
}

TEST_CASE("Hierarchical function call interaction with inst caching") {
    auto& code = R"(
module m;
    function foo;
        foo = 1;
    endfunction
endmodule

module top;
    m m1();
    m m2();

    logic a;
    always_comb begin
        a = m2.foo();
    end
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Multi-assign through iface modports false positive") {
    auto& code = R"(
interface I;
    logic a;
    modport i(input a);
    modport o(output a);
endinterface

module m(I.i incoming, I.o outgoing);
    assign outgoing.a = incoming.a;
endmodule

module top;
    I a(), b(), c();
    m m1(a, b);
    m m2(b, c);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Multi-assign loop unroll in genblk regress") {
    auto& code = R"(
module m #(parameter int p);
    logic [2:0][4*p-1:0] arr;
    for (genvar g = 0; g < p; g++) begin
        localparam int lp = g * 4;
        always_comb begin
            for (int i = 0; i < 3; i++) begin
                arr[i][lp+:2] = '1;
            end
        end
    end
endmodule

module top;
    m #(4) m1();
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}
