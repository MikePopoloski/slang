// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/analysis/AnalysisManager.h"

using namespace slang::analysis;

#define CHECK_DIAGS_EMPTY              \
    do {                               \
        if (!diags.empty()) {          \
            FAIL_CHECK(report(diags)); \
        }                              \
    } while (0)

Diagnostics analyze(const std::string& text, Compilation& compilation) {
    auto tree = SyntaxTree::fromText(text);
    compilation.addSyntaxTree(tree);

    auto diags = compilation.getAllDiagnostics();
    compilation.freeze();

    AnalysisOptions options;
    options.flags = AnalysisFlags::CheckUnused;

    AnalysisManager analysisManager(options);
    analysisManager.analyze(compilation);

    diags.append_range(analysisManager.getDiagnostics(compilation.getSourceManager()));
    return diags;
}

TEST_CASE("Inout ports are treated as readers and writers") {
    auto& text = R"(
interface I;
    wire integer i;
    modport m(inout i);
endinterface

module m(inout wire a);
    wire local_a;
    pullup(local_a);
    tranif1(a, local_a, 1'b1);
endmodule

module top;
    I i();

    wire a;
    m m1(.*);
    m m2(.*);
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Unused var checking intersected with generic classes -- GH #1142") {
    auto& text = R"(
class A #(type T);
endclass

class B #(type T);
    task get((* unused *) output T t);
    endtask
endclass

class C #(type T = int);
    B #(T) b;
    (* unused *) typedef A #(C) unused;

    task test();
        T t;
        forever begin
            b.get(t);
            process(t);
        end
    endtask

    function void process((* unused *) T t);
    endfunction
endclass

module top;
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Diagnose unused modules / interfaces") {
    auto& text = R"(
interface I;
endinterface

interface J;
endinterface

module bar (I i);
endmodule

module top;
endmodule

module top2({a[1:0], a[3:2]});
    ref int a;
endmodule

module top3(ref int a);
    assign a = 1;
endmodule
)";

    CompilationOptions options;
    options.flags = CompilationFlags::None;

    Compilation compilation(options);
    auto diags = analyze(text, compilation);
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::TopModuleIfacePort);
    CHECK(diags[1].code == diag::TopModuleUnnamedRefPort);
    CHECK(diags[2].code == diag::TopModuleRefPort);
    CHECK(diags[3].code == diag::UnusedDefinition);
}

TEST_CASE("Unused nets and vars") {
    auto& text = R"(
module m #(int foo)(input baz, output bar);
    int i;
    if (foo > 1) assign i = 0;

    int x = 1;
    int z;
    int y = x + z;

    wire j = 1;
    wire k;
    wire l = k;
    wire m;

    assign m = 1;
endmodule

module n(ref boz, inout buz, inout biz, inout bxz);
    assign biz = 1;
    (* maybe_unused *) logic n = bxz;
endmodule

module o(ref .a(boz), inout .b(buz), inout .c(biz), inout .d(bxz));
    int boz;
    wire buz,biz,bxz;

    assign biz = 1;
    (* maybe_unused *) logic n = bxz;
endmodule

module top;
    logic baz,bar;
    m #(1) m1(.*);
    m #(2) m2(bar, baz);
    m #(3) m3(a, b);
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    diags = diags.filter({diag::StaticInitOrder, diag::StaticInitValue});
    REQUIRE(diags.size() == 19);
    CHECK(diags[0].code == diag::UnusedPort);
    CHECK(diags[1].code == diag::UndrivenPort);
    CHECK(diags[2].code == diag::UnusedButSetVariable);
    CHECK(diags[3].code == diag::UnassignedVariable);
    CHECK(diags[4].code == diag::UnusedVariable);
    CHECK(diags[5].code == diag::UnusedNet);
    CHECK(diags[6].code == diag::UndrivenNet);
    CHECK(diags[7].code == diag::UnusedNet);
    CHECK(diags[8].code == diag::UnusedButSetNet);
    CHECK(diags[9].code == diag::UnusedPort);
    CHECK(diags[10].code == diag::UnusedPort);
    CHECK(diags[11].code == diag::UnusedButSetPort);
    CHECK(diags[12].code == diag::UndrivenPort);
    CHECK(diags[13].code == diag::UnusedPort);
    CHECK(diags[14].code == diag::UnusedPort);
    CHECK(diags[15].code == diag::UnusedButSetPort);
    CHECK(diags[16].code == diag::UndrivenPort);
    CHECK(diags[17].code == diag::UnusedImplicitNet);
    CHECK(diags[18].code == diag::UnusedImplicitNet);
}

TEST_CASE("Unused nets and vars false positives regress") {
    auto& text = R"(
interface I(input clk);
    logic baz;
    modport m(input clk, baz);
    modport n(output baz);
endinterface

module m(output v);
    wire clk = 1;
    I i(clk);

    int x,z;
    if (0) begin
        assign x = 1;
        always_ff @(posedge clk) v <= x;

        assign z = 1;
    end
    else begin
        assign z = 1;
    end

    wire integer y = z;
    initial $dumpvars(m.y);

    event e[4];
    initial begin
       for (int i = 0; i < 4; i++) begin
           ->e[i];
       end
       @ e[0] begin end
    end

    initial begin
        int b[$];
        static int q = 1;
        string s1;
        s1.itoa(q);
        b.push_back(1);
    end
endmodule

(* unused *) module n #(parameter int i)(input x, output y, output z);
    logic [i-1:0] a = 1;
    assign y = a[x];
endmodule

package p;
    int i;
endpackage

module q(
    output logic [7:0] lhs,
    input  logic [7:0] rhs,
    input  logic [2:0] lhs_lsb,
    input  logic [2:0] rhs_lsb
);
   always_comb begin
       lhs = 0;
       lhs[lhs_lsb +: 2] = rhs[rhs_lsb +: 2];
   end

   wire w, x;
   tranif1(w, x, 1'b1);
endmodule

class C;
    extern function int foo(int a);
    virtual function bar(int b);
        int c[$];
        c.push_back(1);
        return 0;
    endfunction
endclass

function int C::foo(int a);
    return a;
endfunction

import "DPI-C" function void dpi_func(int i);

class D;
    int s1[$];
    int s2[int];
    function void f();
        int i = 0;
        foreach (s2[j]) begin
            int k = j * 4;
            s1[i++] = k;
        end
    endfunction
endclass
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Ref args are considered used") {
    auto& text = R"(
class C;
    function void f1(ref bit [3:0] a);
        a = 4'hF;
    endfunction

    function int unsigned f2();
        bit [3:0] a;
        f1(a);
        return 0;
    endfunction
endclass

module top;
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("'unused' warnings with clock vars") {
    auto& text = R"(
interface I;
    logic clk;
    logic a;

    clocking cb @(posedge clk);
        input a;
    endclocking
endinterface

class TB;
    virtual I intf;
    task run();
        @(intf.cb);
        if (intf.cb.a) begin
            $display("error!");
        end
    endtask
endclass

module M(
    input logic clk,
    output logic a
);
   always_ff @(posedge clk) begin
       a <= 1'b1;
   end
endmodule

module top;
    logic a;
    logic clk;
    I i();

    M m(.*);

    assign i.clk = clk;
    assign i.a = a;

    initial begin
        clk = 0;
        forever begin
            #1ns;
            clk = ~clk;
        end
    end
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("'unassigned' warnings with clockvar outputs") {
    auto& text = R"(
interface I;
    logic clk;
    logic a;

    clocking cb_driver @(posedge clk);
        output a;
    endclocking
endinterface

class C;
    virtual I i;
    task drive();
        @(i.cb_driver);
        i.cb_driver.a <= 1'b0;
    endtask

    logic q = i.a;
endclass

module top;
   I i();
   C c;
   initial begin
       i.clk = 0;
       forever begin
           #1ns i.clk = ~i.clk;
       end
   end
   initial begin
       c = new();
       c.i = i;
       c.drive();
   end
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Unused function args") {
    auto& text = R"(
function foo(input x, output y);
    y = 1;
    return 0;
endfunction

module m;
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UnusedArgument);
}

TEST_CASE("System function args count as outputs") {
    auto& text = R"(
class C;
    function bit f();
        bit a;
        int rc = std::randomize(a);
        assert(rc != 0);
        return a;
    endfunction
endclass

module m;
    int i;
    string a = "foo", s = "a 3";
    int b = 0;
    initial begin
        $cast(i, i);
        void'($sscanf(s, "%s %d", a, b));
    end

    (* unused *) int q = b + a.len;
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Class handle access 'unused' warnings") {
    auto& text = R"(
class A;
    int i;
endclass

class C;
    task t1(A a);
        a.i = 3;
    endtask

    task t2(A a);
        A a1 = a;
        a1.i = 3;
    endtask
endclass

module m;
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Virtual interface handle access 'unused' warnings") {
    auto& text = R"(
interface I;
    logic clk;
endinterface

class C;
    event sys_clk;

    virtual I i;
    function virtual I get_intf();
        return i;
    endfunction

    task t();
        virtual I intf = get_intf();
        @(intf.clk);
        ->sys_clk;
    endtask
endclass

module top;
    I intf();
    initial begin
        intf.clk = 0;
        forever begin
            #1ns;
            intf.clk = ~intf.clk;
        end
    end
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Exclude 'unused' warnings based on attributes, underscore name") {
    auto& text = R"(
module m;
    int _;
    (* maybe_unused *) int foo;
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Unused parameters") {
    auto& text = R"(
module m #(parameter p = 1, q = 2, parameter type t = int, u = real);
    (* unused *) u r = 3.14;
    (* unused *) int i = q;
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UnusedParameter);
    CHECK(diags[1].code == diag::UnusedTypeParameter);
}

TEST_CASE("Unused typedefs") {
    auto& text = R"(
class C;
    parameter p = 1;
endclass

module m;
    typedef struct { int a, b; } asdf;
    typedef enum { A, B } foo;

    (* unused *) foo f = A;

    typedef C D;
    (* unused *) parameter p = D::p;

    typedef enum { E, F } bar;

    (* unused *) parameter q = E;
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UnusedTypedef);
}

TEST_CASE("Covergroups and class handles are 'used' if constructed") {
    auto& text = R"(
interface I;
    logic a = 1;
    covergroup cg;
        a: coverpoint a;
    endgroup

    cg cov = new();
endinterface

class C;
    function new; $display("Hello!"); endfunction
endclass

module m;
    I i();
    C c1 = new;
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Unused genvars") {
    auto& text = R"(
module m;
    genvar g;
    genvar h;
    for (g = 0; g < 3; g++) begin end
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UnusedGenvar);
}

TEST_CASE("Unused assertion decls") {
    auto& text = R"(
module m(input clk);
    sequence s1; 1; endsequence
    property p1; 1; endproperty
    let l1 = 1;

    sequence s2; 1; endsequence
    property p2; 1; endproperty
    let l2 = 1;

    assert property (@(posedge clk) s2);
    assert property (@(posedge clk) p2);
    (* unused *) int i = l2();
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::UnusedAssertionDecl);
    CHECK(diags[1].code == diag::UnusedAssertionDecl);
    CHECK(diags[2].code == diag::UnusedAssertionDecl);
}

TEST_CASE("Unused imports") {
    auto& text = R"(
package p;
    int a;
endpackage

module m;
    import p::a;
    import p::*;
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UnusedImport);
    CHECK(diags[1].code == diag::UnusedWildcardImport);
}

TEST_CASE("Not gate undriven warning regress GH #1227") {
    auto& text = R"(
module test (Y, A);
  output Y;
  input A;
wire B;
not (B, A);
not (Y, B);
endmodule
)";

    Compilation compilation;
    auto diags = analyze(text, compilation);
    CHECK_DIAGS_EMPTY;
}
