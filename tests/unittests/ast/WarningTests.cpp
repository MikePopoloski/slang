// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

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
    REQUIRE(diags.size() == 7);
    CHECK(diags[0].code == diag::CaseOutsideRange);
    CHECK(diags[1].code == diag::CaseTypeMismatch);
    CHECK(diags[2].code == diag::CaseTypeMismatch);
    CHECK(diags[3].code == diag::CaseTypeMismatch);
    CHECK(diags[4].code == diag::CaseOutsideRange);
    CHECK(diags[5].code == diag::CaseTypeMismatch);
    CHECK(diags[6].code == diag::CaseTypeMismatch);
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
