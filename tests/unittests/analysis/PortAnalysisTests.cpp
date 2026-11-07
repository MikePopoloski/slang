// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "AnalysisTests.h"

TEST_CASE("Inconsistent port collapsing") {
    auto& code = R"(
module m (input .a({b, {c[1:0], d}}), input uwire [2:1] f);
    wand b;
    wand [3:0] c;
    supply0 d;
endmodule

module n ({b[1:0], a});
    input tri0 a;
    input tri1 [3:0] b;
endmodule

module x(input trireg in);
    y y(.in);
    y y1(in);
    y y2(.in(in));
endmodule

module y(input wor in);
endmodule

module top;
    wand a;
    wor b;
    trireg [1:0] c;

    m m1({a, b, c}, c);
    n n1({{a, a}, c[0]});
    x x1(b);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::ImplicitConnNetInconsistent);
    CHECK(diags[1].code == diag::NetInconsistent);
    CHECK(diags[2].code == diag::NetInconsistent);
    CHECK(diags[3].code == diag::NetRangeInconsistent);
    CHECK(diags[4].code == diag::NetRangeInconsistent);
    CHECK(diags[5].code == diag::NetInconsistent);
    CHECK(diags[6].code == diag::NetInconsistent);
    CHECK(diags[7].code == diag::NetInconsistent);
}

TEST_CASE("User-defined nettype port connection errors") {
    auto& code = R"(
nettype integer nt1;

module m(nt1 foo, bar, input nt1 baz);
endmodule

module n(input signed foo);
endmodule

module o(nt1 a);
endmodule

module p({a, b});
    input nt1 a, b;
endmodule

module q(input .foo({a, b}));
    nt1 a;
    wire b;
endmodule

module top;
    wire signed [5:0] a;
    wire integer b;

    m m1(a, b, b);

    nettype logic signed[5:0] nt2;
    nt2 c;
    n n1(c);

    o o1(c);

    p p1({c, c});

    nt1 d;
    p p2({d, d});

    q q1({c, c});
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::MismatchedUserDefPortConn);
    CHECK(diags[1].code == diag::MismatchedUserDefPortDir);
    CHECK(diags[2].code == diag::MismatchedUserDefPortConn);
    CHECK(diags[3].code == diag::UserDefPortTwoSided);
    CHECK(diags[4].code == diag::UserDefPortTwoSided);
    CHECK(diags[5].code == diag::UserDefPortMixedConcat);
}

TEST_CASE("Interconnect port connected to variable") {
    auto& code = R"(
module p(input interconnect a);
endmodule

module top;
    logic a;
    p p1(.a);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::InterconnectPortVar);
}

TEST_CASE("Interconnect net collapsing cross-module assignments") {
    auto& code = R"(
module netlist;
  interconnect w;
  dut4 child4();
  dut2 child1(w);
  dut3 child3(w);
endmodule

module dut1(output wand w);
  assign w = 1;
endmodule

module dut2(output wor w);
  assign w = 0;
endmodule

module dut3(input wire w);
  initial #10 $display(w);
endmodule

module dut4;
  dut1 child2(netlist.w);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Multi-port with an invalid component still resolves all ports") {
    auto tree = SyntaxTree::fromText(R"(
module n ({b[1:4], a});
    input tri0 a;
    input tri1 [3:0] b;
endmodule

module top;
    wire [1:0] c;
    n n1(c);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::RangeSelectReversed);

    compilation.freeze();

    AnalysisManager analysisManager;
    analysisManager.analyze(compilation);
}

TEST_CASE("Modport expression drivers retargeted across interface instances with enums") {
    auto& code = R"(
interface J;
    typedef enum logic [1:0] { A, B } e_t;
    e_t [2:0] b;
    enum logic [1:0] { C, D } [2:0] c;
    struct packed { e_t x; } s;
    e_t u[2];
    modport m(output .R(b[1:0]), output .S(c), output .T(s), output .U(u[1]));
endinterface

module n(J.m j);
    assign j.R = 0;
    assign j.S = 0;
    assign j.T = 0;
    assign j.U = type(j.U)'(0);
endmodule

module top;
    J j1(), j2();
    n n1(j1), n2(j2);
endmodule
)";

    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Modport drivers retargeted across instances with an inline enum base type") {
    auto tree = SyntaxTree::fromText(R"(
interface J;
    enum enum { Z } [1:0] { C, D } [2:0] c;
    modport m(output .S(c));
endinterface

module n(J.m j);
    assign j.S = 0;
endmodule

module top;
    J j1(), j2();
    n n1(j1), n2(j2);
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ExpectedEnumBase);

    compilation.freeze();

    AnalysisManager analysisManager;
    analysisManager.analyze(compilation);
}
