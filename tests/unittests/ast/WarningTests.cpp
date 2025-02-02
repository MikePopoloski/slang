// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

TEST_CASE("Diagnose unused modules / interfaces") {
    auto tree = SyntaxTree::fromText(R"(
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
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::UnusedDefinition);
    CHECK(diags[1].code == diag::TopModuleIfacePort);
    CHECK(diags[2].code == diag::TopModuleUnnamedRefPort);
    CHECK(diags[3].code == diag::TopModuleRefPort);
}

TEST_CASE("Unused nets and vars") {
    auto tree = SyntaxTree::fromText(R"(
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
)");

    CompilationOptions coptions;
    coptions.flags &= ~CompilationFlags::SuppressUnused;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);

    auto diags = compilation.getAllDiagnostics().filter(
        {diag::StaticInitOrder, diag::StaticInitValue});

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
    auto tree = SyntaxTree::fromText(R"(
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
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Ref args are considered used") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    function void f1(ref bit [3:0] a);
        a = 4'hF;
    endfunction

    function int unsigned f2();
        bit [3:0] a;
        f1(a);
    endfunction
endclass

module top;
endmodule
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("'unused' warnings with clock vars") {
    auto tree = SyntaxTree::fromText(R"(
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
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("'unassigned' warnings with clockvar outputs") {
    auto tree = SyntaxTree::fromText(R"(
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
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Unused function args") {
    auto tree = SyntaxTree::fromText(R"(
function foo(input x, output y);
    y = 1;
endfunction

module m;
endmodule
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UnusedArgument);
}

TEST_CASE("System function args count as outputs") {
    auto tree = SyntaxTree::fromText(R"(
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
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Class handle access 'unused' warnings") {
    auto tree = SyntaxTree::fromText(R"(
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
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Virtual interface handle access 'unused' warnings") {
    auto tree = SyntaxTree::fromText(R"(
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
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Exclude 'unused' warnings based on attributes, underscore name") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int _;
    (* maybe_unused *) int foo;
endmodule
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Unused parameters") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter p = 1, q = 2, parameter type t = int, u = real);
    (* unused *) u r = 3.14;
    (* unused *) int i = q;
endmodule
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UnusedParameter);
    CHECK(diags[1].code == diag::UnusedTypeParameter);
}

TEST_CASE("Unused typedefs") {
    auto tree = SyntaxTree::fromText(R"(
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
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UnusedTypedef);
}

TEST_CASE("Covergroups and class handles are 'used' if constructed") {
    auto tree = SyntaxTree::fromText(R"(
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
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Unused genvars") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    genvar g;
    genvar h;
    for (g = 0; g < 3; g++) begin end
endmodule
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UnusedGenvar);
}

TEST_CASE("Unused assertion decls") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    sequence s1; 1; endsequence
    property p1; 1; endproperty
    let l1 = 1;

    sequence s2; 1; endsequence
    property p2; 1; endproperty
    let l2 = 1;

    assert property (s2);
    assert property (p2);
    (* unused *) int i = l2();
endmodule
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::UnusedAssertionDecl);
    CHECK(diags[1].code == diag::UnusedAssertionDecl);
    CHECK(diags[2].code == diag::UnusedAssertionDecl);
}

TEST_CASE("Unused imports") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    int a;
endpackage

module m;
    import p::a;
    import p::*;
endmodule
)");

    CompilationOptions coptions;
    coptions.flags = CompilationFlags::None;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UnusedImport);
    CHECK(diags[1].code == diag::UnusedWildcardImport);
}

TEST_CASE("Implicit conversions with constants") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [9:0] a = 9000;
    shortint b = -32769;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::ConstantConversion);
    CHECK(diags[1].code == diag::ConstantConversion);
}

TEST_CASE("Diagnostic disambiguation via differing params") {
    auto tree = SyntaxTree::fromText(R"(
module m #(parameter int p);
    logic [p-1:0] a;
    assign a = 32'hffffffff;
endmodule

module top;
    m #(4) m1();
    m #(5) m2();
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    CHECK("\n" + report(diags) == R"(
  in instance: top.m1
source:4:14: warning: implicit conversion from 'logic[31:0]' to 'logic[3:0]' changes value from 32'd4294967295 to 4'b1111 [-Wconstant-conversion]
    assign a = 32'hffffffff;
             ^ ~~~~~~~~~~~~
  in instance: top.m2
source:4:14: warning: implicit conversion from 'logic[31:0]' to 'logic[4:0]' changes value from 32'd4294967295 to 5'b11111 [-Wconstant-conversion]
    assign a = 32'hffffffff;
             ^ ~~~~~~~~~~~~
)");
}

TEST_CASE("Constant conversion to/from reals") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i = 3.14;
    int j = shortreal'(3.14);
    real k = 3;
    shortreal l = 16777217;
    shortreal n = 3.14;
    shortreal o = 16777217.123;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::ConstantConversion);
    CHECK(diags[1].code == diag::ConstantConversion);
    CHECK(diags[2].code == diag::ConstantConversion);
}

TEST_CASE("Assigning member to union does not warn") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef struct packed {
        logic a, b;
    } s_t;
    s_t s;

    union packed {
        s_t s;
        logic [1:0] l;
    } u;

    struct packed { logic d, e; } other;

    initial begin
        u = s;
        u = other;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ImplicitConvert);
}

TEST_CASE("Sign conversion warnings in constexprs") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    typedef logic [1:0] l2;
    logic signed [1:0] i = l2'(3);
    logic signed [1:0] j = 2'd3;
    logic signed [1:0] k = '1;
    logic signed [1:0] l = (2'd3:2'd1:-3);
    logic signed m = (2'd1 == 2'd1);
    logic signed [1:0] n = 2'd1 << 1;
    logic signed [1:0] o = +2'd3;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::SignConversion);
    CHECK(diags[1].code == diag::SignConversion);
    CHECK(diags[2].code == diag::SignConversion);
    CHECK(diags[3].code == diag::SignConversion);
}

TEST_CASE("Edge of multibit type") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    always @(posedge i) begin end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::MultiBitEdge);
}

TEST_CASE("Implicit boolean conversion warnings") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    real r;
    initial if (r) begin end

    int i;
    initial if (i + 2) begin end
    initial if (i || r) begin end

    // These don't warn
    initial if (i >> 2) begin end
    initial if (i & 2) begin end
    initial if (i ^ 2) begin end
endmodule

class C;
    int a;
    constraint c {
        if (a) {}
    }
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::FloatBoolConv);
    CHECK(diags[1].code == diag::IntBoolConv);
    CHECK(diags[2].code == diag::IntBoolConv);
    CHECK(diags[3].code == diag::FloatBoolConv);
    CHECK(diags[4].code == diag::IntBoolConv);
}

TEST_CASE("Useless cast warnings") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i, j;
    assign i = int'(j);

    logic [3:0] k, l;
    assign k = 4'(l);

    logic [7:0] n;
    assign n = type(n)'({k, l});

    // This one isn't useless.
    typedef int DA[];
    localparam p1 = DA'({1, 2, 3});

    // This one is.
    localparam DA p2 = DA'({1, 2, 3});

    // Not useless.
    localparam p3 = DA'(1 ? '{1, 2, 3} : p1);

    // Useless.
    localparam p4 = int'(1 ? 2 : 3);

    // Not useless.
    typedef logic [31:0] data_t;
    logic [31:0] a;
    data_t b;
    assign b = data_t'(a);

    // Not useless.
    localparam width = 32;
    logic [1:0][width-1:0] c;
    for (genvar i = 0; i < 2; i++) begin
        always_comb c[i] = $bits(c[i])'(i);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    for (size_t i = 0; i < 5; i++)
        CHECK(diags[i].code == diag::UselessCast);
}

TEST_CASE("Propagated type conversion warnings point to the right operator") {
    auto tree = SyntaxTree::fromText(R"(
function f1(int i);
    return (i >>> 31) == '1;
endfunction

function automatic int f2(int i);
    int unsigned j;
    j += (i + 31);
    return j;
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 5);
    CHECK(diags[0].code == diag::SignConversion);
    CHECK(diags[1].code == diag::UnsignedArithShift);
    CHECK(diags[2].code == diag::ArithOpMismatch);
    CHECK(diags[3].code == diag::SignConversion);
    CHECK(diags[4].code == diag::SignConversion);
}

TEST_CASE("Indeterminate variable initialization order") {
    auto tree = SyntaxTree::fromText(R"(
package p;
    int i = 1;
endpackage

int h = 1;

module m(input int port);
    import p::*;
    int j = port;
    int k = i;
    int l = h;
    wire integer m;
    int n = m;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::StaticInitValue);
    CHECK(diags[1].code == diag::StaticInitOrder);
    CHECK(diags[2].code == diag::StaticInitValue);
}

TEST_CASE("Float conversion warnings") {
    auto tree = SyntaxTree::fromText(R"(
function automatic f(real r);
    int i = r;
    shortreal s = r;
    real t = i;
    real u = s;
endfunction
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::FloatIntConv);
    CHECK(diags[1].code == diag::FloatNarrow);
    CHECK(diags[2].code == diag::IntFloatConv);
    CHECK(diags[3].code == diag::FloatWiden);
}

TEST_CASE("Binary operator warnings") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    struct packed { logic a; } a;
    int i;
    int unsigned j;
    real r;

    initial begin
        if (0 == a) begin end
        i = i + j;
        if (i == r) begin end
        if (i < j) begin end
        if (a & j) begin end
    end

    localparam int x = 3;
    localparam real y = 4.1;
    localparam real z = x + y * x;

    localparam int unsigned NUM_PORTS = 3;
    genvar g;
    for (g = 0; g < NUM_PORTS; g++) begin end
endmodule

class C;
    typedef enum int {
        A = 0,
        C = 2,
        E = 4
    } e_t;

    rand bit v[$];

    constraint q {
        v.size() == E;
    }
endclass

module top;
    logic valid;
    logic [7:0] a;
    logic [7:0] b;

    // No warning for sign comparison of genvars.
    for (genvar i = 0; i < 8; i++) begin
        always_comb a[i] = valid && i == b;
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::SignConversion);
    CHECK(diags[1].code == diag::ArithOpMismatch);
    CHECK(diags[2].code == diag::IntFloatConv);
    CHECK(diags[3].code == diag::ComparisonMismatch);
    CHECK(diags[4].code == diag::SignCompare);
    CHECK(diags[5].code == diag::BitwiseOpMismatch);
}

TEST_CASE("Binary operator with struct type preserves the type") {
    auto tree = SyntaxTree::fromText(R"(
module top;
  typedef struct packed {
      logic [1:0] a;
      logic [1:0] b;
  } s_t;

  s_t a, b, c, d;

  always_comb begin
      d = a |  b | c;
  end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Parentheses / precedence warnings") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int unsigned flags;
    logic a, b, c;
    int unsigned d, e;
    initial begin
        if (flags & 'h1 == 'h1) begin end
        if (a & b | c) begin end
        if (a | b ^ c) begin end
        if (a || b && c) begin end
        if (a << 1 + 1) begin end
        if (!d < e) begin end
        if (!d & e) begin end
        if ((a + b ? 1 : 2) == 2) begin end
        if (a < b < c) begin end
        c |= a & b;
        if (!a inside {0, 1, 0}) begin end
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 11);
    CHECK(diags[0].code == diag::BitwiseRelPrecedence);
    CHECK(diags[1].code == diag::BitwiseOpParentheses);
    CHECK(diags[2].code == diag::BitwiseOpParentheses);
    CHECK(diags[3].code == diag::LogicalOpParentheses);
    CHECK(diags[4].code == diag::ArithInShift);
    CHECK(diags[5].code == diag::LogicalNotParentheses);
    CHECK(diags[6].code == diag::LogicalNotParentheses);
    CHECK(diags[7].code == diag::BitwiseOpMismatch);
    CHECK(diags[8].code == diag::ConditionalPrecedence);
    CHECK(diags[9].code == diag::ConsecutiveComparison);
    CHECK(diags[10].code == diag::LogicalNotParentheses);
}

TEST_CASE("Case statement type warnings") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    enum{A,B,C} e;
    enum{D,E,F} f;
    int unsigned g;
    logic [1:0] h;
    parameter [99:0] P = 999999;
    initial begin
        case (e)
            A, f: ;
            F, 1: ;
            3.14: ;
            default;
        endcase
        case (1)
            g, h: ;
            default;
        endcase
        case (g)
            P: ;
            4'd1:;
        endcase
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::IntFloatConv);
    CHECK(diags[1].code == diag::CaseTypeMismatch);
    CHECK(diags[2].code == diag::IntFloatConv);
    CHECK(diags[3].code == diag::CaseTypeMismatch);
    CHECK(diags[4].code == diag::CaseTypeMismatch);
    CHECK(diags[5].code == diag::CaseTypeMismatch);
    CHECK(diags[6].code == diag::CaseDefault);
}

TEST_CASE("Case statement out of range") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [2:0] a;
    initial begin
        casex (a)
            4'b01: ;
            4'b1000: ;
            -1: ;
            4'bx001: ;
            default;
        endcase
        case (4'b1000)
            a: ;
            default;
        endcase
        casez (a)
            4'b?001: ;
            default;
        endcase
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::CaseOutsideRange);
    CHECK(diags[1].code == diag::CaseTypeMismatch);
    CHECK(diags[2].code == diag::CaseTypeMismatch);
    CHECK(diags[3].code == diag::CaseTypeMismatch);
    CHECK(diags[4].code == diag::CaseOverlap);
    CHECK(diags[5].code == diag::CaseOutsideRange);
    CHECK(diags[6].code == diag::CaseTypeMismatch);
    CHECK(diags[7].code == diag::CaseTypeMismatch);
}

TEST_CASE("Case statement missing enum values") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    enum {A,B,C,D,E} e;
    initial begin
        case (e)
            A, B, C, D:;
            default;
        endcase
        case (e)
            A, B, C:;
            default;
        endcase
        case (e)
            A, B:;
            default;
        endcase
        case (e)
            A:;
            default;
        endcase

        case (e)
            A, B, C, D:;
        endcase
        case (e)
            A, B, C:;
        endcase
        case (e)
            A, B:;
        endcase
        case (e)
            A:;
        endcase
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 12);
    CHECK(diags[0].code == diag::CaseEnumExplicit);
    CHECK(diags[1].code == diag::CaseEnumExplicit);
    CHECK(diags[2].code == diag::CaseEnumExplicit);
    CHECK(diags[3].code == diag::CaseEnumExplicit);
    CHECK(diags[4].code == diag::CaseDefault);
    CHECK(diags[5].code == diag::CaseEnum);
    CHECK(diags[6].code == diag::CaseDefault);
    CHECK(diags[7].code == diag::CaseEnum);
    CHECK(diags[8].code == diag::CaseDefault);
    CHECK(diags[9].code == diag::CaseEnum);
    CHECK(diags[10].code == diag::CaseDefault);
    CHECK(diags[11].code == diag::CaseEnum);
}

TEST_CASE("Case statement dups") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    int i;
    event e;
    initial begin
        case (i)
            1, 2:;
            3, 1:;
            default;
        endcase
        case (e)
            null:;
            null:;
            default;
        endcase
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::CaseDup);
    CHECK(diags[1].code == diag::CaseDup);
}

TEST_CASE("Case statement overlap") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [65:0] a;
    initial begin
        casex (a)
            65'bx1011z:;
            65'b10111:;
            65'b11011:;
            65'b1101x:;
            65'b110?1:;
            default;
        endcase
        casez (a)
            65'bx1111:;
            65'b1x111:;
            65'b1?111:;
            65'b?1111:;
            65'b?0111:;
            default;
        endcase
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::CaseOverlap);
    CHECK(diags[1].code == diag::CaseOverlap);
    CHECK(diags[2].code == diag::CaseOverlap);
    CHECK(diags[3].code == diag::CaseZWithX);
    CHECK(diags[4].code == diag::CaseZWithX);
    CHECK(diags[5].code == diag::CaseOverlap);
    CHECK(diags[6].code == diag::CaseOverlap);
}

TEST_CASE("Case statement with huge bit width selector") {
    auto tree = SyntaxTree::fromText(R"(
module test9(
  input reg [100:0] sel_i,
  input reg trg_i,
  output reg [1:0] reg_o
);
  always @(posedge trg_i) begin
    casex (sel_i)
      -12'b00zzzzz00001,
      12'b11: reg_o = 2'b01;
    endcase
  end
endmodule

module test10(
  input reg [100:0] sel_i,
  input reg trg_i,
  output reg [1:0] reg_o
);
  always @(posedge trg_i) begin
    casex (sel_i)
      12'sb00xxxxx00001,
      -12'b00zzzzz00001,
      12'b11: reg_o = 2'b01;
    endcase
  end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::CaseDefault);
    CHECK(diags[1].code == diag::CaseOverlap);
    CHECK(diags[2].code == diag::CaseDefault);
    CHECK(diags[3].code == diag::CaseOverlap);
}

TEST_CASE("Case items with unknowns that are not wildcards") {
    auto tree = SyntaxTree::fromText(R"(
module m;
    logic [3:0] a;
    initial begin
        case (a)
            4'b?10:;
            4'bx10:;
            default;
        endcase
        casez (a)
            4'bx10:;
            default;
        endcase
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::CaseNotWildcard);
    CHECK(diags[1].code == diag::CaseNotWildcard);
    CHECK(diags[2].code == diag::CaseZWithX);
}

TEST_CASE("Conversion warnings in conditional operator") {
    auto tree = SyntaxTree::fromText(R"(
module test;
  initial begin
    static int a = 3;
    static int b = 5;
    static bit cond = 1;
    static longint result = 7;
    result = cond ? a : b;
  end
endmodule

module test2;
  initial begin
    static int a = 3;
    static int b = 5;
    static bit cond = 1;
    static longint result = 7;
    bit c, d;

    result = cond ? a : longint'(b);

    // This should not warn.
    c = cond ? d : 0;
  end
endmodule

module test3;
    localparam int unsigned SIZE = 16;

    logic a;
    logic [7:0] b, c;
    logic [SIZE-1:0] d, e, f, g;

    always_comb begin
        d = SIZE'( a ? b : c);
        e = SIZE'(b);
        f = a ? SIZE'(b) : SIZE'(c);
        g = SIZE'( (a == 0) ? f : c);
    end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::WidthExpand);
    CHECK(diags[1].code == diag::WidthExpand);
    CHECK(diags[2].code == diag::WidthExpand);
}

TEST_CASE("Not gate undriven warning regress GH #1227") {
    auto tree = SyntaxTree::fromText(R"(
module test (Y, A);
  output Y;
  input A;
wire B;
not (B, A);
not (Y, B);
endmodule
)");

    CompilationOptions coptions;
    coptions.flags &= ~CompilationFlags::SuppressUnused;

    Compilation compilation(coptions);
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}
