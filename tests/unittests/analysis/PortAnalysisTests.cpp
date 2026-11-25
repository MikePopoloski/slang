// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "AnalysisTests.h"
#include <map>

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
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::RangeSelectReversed);
    CHECK(diags[1].code == diag::PortWidthExpand);

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

static Diagnostics analyzeInstanceDrivers(const std::string& code, Compilation& compilation) {
    AnalysisOptions options;
    options.flags = AnalysisFlags::CheckInstanceDrivers;
    AnalysisManager analysisManager(options);
    return analyze(code, compilation, analysisManager);
}

static std::string undrivenArg(const Diagnostic& diag) {
    REQUIRE(diag.code == diag::PartiallyUndrivenPort);
    REQUIRE(diag.args.size() == 2);
    return std::get<std::string>(diag.args[1]);
}

TEST_CASE("Output ports undriven in a specific instance") {
    auto& code = R"(
module testing #(parameter COND_A = 0) (output logic a);
    if (COND_A) begin : cond_a
        assign a = 0;
    end
    else begin : default_case
    end
endmodule

module m(output logic a);
    always_comb a = 1'b1;
endmodule

module n #(bit [3:0] P = 4'hE) (output logic [3:0] a);
    for (genvar i = 0; i < 4; i++) begin : index
        if (P[i]) begin : valid
            m m1(.a(a[i]));
        end
    end
endmodule

module top;
    logic a, b;
    logic [3:0] c, d;
    testing t1(.a);
    testing #(.COND_A(1)) t2(.a(b));
    n n1(.a(c));
    n #(.P(4'hF)) n2(.a(d));
endmodule
)";

    Compilation compilation;
    auto diags = analyzeInstanceDrivers(code, compilation);
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UndrivenPortInstance);
    CHECK(undrivenArg(diags[1]) == "a[0]");

    // Without the flag nothing is reported.
    Compilation compilation2;
    AnalysisManager analysisManager;
    diags = analyze(code, compilation2, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Partially undriven output port descriptions") {
    auto& code = R"(
typedef struct packed { logic a; logic [1:0] b; logic c; } s_t;
typedef struct packed { struct packed { logic a; logic [1:0] b; } in; logic [3:0] c; } ns_t;
typedef struct { logic a; logic [1:0] b; } us_t;
typedef struct { logic [3:0] arr [2]; int x; } ua_t;
typedef struct { real r; logic [3:0] v; } ur_t;
typedef enum logic [3:0] { A, B } e_t;
typedef enum logic [0:3] { C, D } ea_t;
typedef union packed { logic [7:0] a; logic [7:0] b; } pu_t;
typedef union { logic [7:0] a; logic [3:0] b; } uu_t;

module m(
    output logic [7:0] v1,
    output logic [7:4] v2,
    output logic [1:4] v3,
    output logic [7:0] v4,
    output logic [0:7] v5,
    output logic [3:0] u1 [2:5],
    output logic [3:0] u2 [5:2],
    output logic c1 [8],
    output logic [3:0][1:0] p1,
    output logic [0:3][1:0] p2,
    output logic [3:0][3:0] p3,
    output logic [1:4][1:0] p4,
    output logic [1:0] u3 [3:0][0:1],
    output logic [7:0] m1 [2],
    output logic [7:0] q [2],
    output logic [7:0] r [1:0],
    output s_t s,
    output ns_t ns,
    output us_t us,
    output ua_t ua,
    output ur_t ur,
    output s_t sa [2],
    output s_t [1:0] ps,
    output byte by,
    output integer ig,
    output int i2,
    output e_t en,
    output ea_t ea,
    output pu_t pu,
    output uu_t uu,
    output logic big [0:1048575],
    output logic one,
    output logic [3:0] full
);
    assign v1[3:0] = 0;
    assign v2[5:4] = 0;
    assign v3[1:2] = 0;
    assign v4[0] = 0; assign v4[4:3] = 0;
    assign v5[1] = 0; assign v5[4:5] = 0;
    assign u1[3] = 0; assign u1[4][1:0] = 0;
    assign u2[3] = 0; assign u2[4][1:0] = 0;
    assign c1[3] = 0;
    assign p1[3] = 0; assign p1[1][0] = 0;
    assign p2[0] = 0; assign p2[2][1] = 0;
    assign p3[0][1:0] = 0;
    assign p4[1][0] = 0; assign p4[3] = 0; assign p4[4][1] = 0;
    assign u3[3][0] = 0; assign u3[2][1][1] = 0; assign u3[0] = '{default:0};
    assign m1[0][2] = 0; assign m1[0][5] = 0; assign m1[1] = 0;
    assign q[0][5:0] = 0; assign q[1][3:2] = 0; assign q[1][7:6] = 0;
    assign r[1][5:0] = 0; assign r[0][3:2] = 0; assign r[0][7:6] = 0;
    assign s.a = 1; assign s.b[1] = 1;
    assign ns.in.b[1] = 0; assign ns.c[3:2] = 0;
    assign us.a = 1;
    assign ua.arr[1] = 0; assign ua.x[7:0] = 0;
    assign ur.v = 0;
    assign sa[0] = 0; assign sa[1].a = 0;
    assign ps[0] = 0; assign ps[1].c = 0;
    assign by[3:0] = 0;
    assign ig[31:1] = 0;
    assign i2[0] = 0; assign i2[8] = 0; assign i2[31:16] = 0;
    assign en[1:0] = 0;
    assign ea[0] = 0; assign ea[2] = 0;
    assign pu.a[3:0] = 0;
    assign uu.b = 0;
    assign big[5] = 0;
    assign one = 0;
    assign full[1:0] = 0; assign full[3:2] = 0;
endmodule
)";

    Compilation compilation;
    auto diags = analyzeInstanceDrivers(code, compilation);

    std::map<std::string, std::string> results;
    for (auto& diag : diags) {
        REQUIRE(diag.code == diag::PartiallyUndrivenPort);
        results[std::get<std::string>(diag.args[0])] = undrivenArg(diag);
    }

    std::map<std::string, std::string> expected = {
        // Vectors: nonzero bounds, ascending ranges, multiple gaps.
        {"v1", "v1[7:4]"},
        {"v2", "v2[7:6]"},
        {"v3", "v3[3:4]"},
        {"v4", "v4[2:1], v4[7:5]"},
        {"v5", "v5[0], v5[2:3], v5[6:7]"},
        // Unpacked arrays in both directions; results are in ascending index order.
        {"u1", "u1[2], u1[4][3:2], u1[5]"},
        {"u2", "u2[2], u2[4][3:2], u2[5]"},
        {"c1", "c1[0:2], c1[4:7]"},
        // Multi-dimensional packed and unpacked arrays.
        {"p1", "p1[0], p1[1][1], p1[2]"},
        {"p2", "p2[1], p2[2][0], p2[3]"},
        {"p3", "p3[0][3:2], p3[3:1]"},
        {"p4", "p4[1][1], p4[2], p4[4][0]"},
        {"u3", "u3[1], u3[2][0], u3[2][1][0], u3[3][1]"},
        // Multiple gaps landing in the same element, in both storage orders.
        {"m1", "m1[0][1:0], m1[0][4:3], m1[0][7:6]"},
        {"q", "q[0][7:6], q[1][1:0], q[1][5:4]"},
        {"r", "r[0][1:0], r[0][5:4], r[1][7:6]"},
        // Structs, nested structs, and arrays of / in structs.
        {"s", "s.b[0], s.c"},
        {"ns", "ns.in.a, ns.in.b[0], ns.c[1:0]"},
        {"us", "us.b"},
        {"ua", "ua.arr[0], ua.x[31:8]"},
        {"ur", "ur.r"},
        {"sa", "sa[1].b, sa[1].c"},
        {"ps", "ps[1].a, ps[1].b"},
        // Other integral types.
        {"by", "by[7:4]"},
        {"ig", "ig[0]"},
        {"i2", "i2[7:1], i2[15:9]"},
        {"en", "en[3:2]"},
        {"ea", "ea[1], ea[3]"},
        // Unions: packed unions are described by bits, unpacked as a whole.
        {"pu", "pu[7:4]"},
        {"uu", "uu"},
        // Large arrays are described without enumerating every element.
        {"big", "big[0:4], big[6:1048575]"},
    };

    CHECK(results == expected);
}

TEST_CASE("Output ports with non-obvious drivers are not undriven") {
    auto& code = R"(
module m(output logic a, output logic [3:0] b, output tri1 c, output logic d = 0,
         output logic e, output wire f, output logic g, output logic h,
         output logic _, (* unused *) output logic j, output logic k);
    always_comb a = 1;
    initial for (int idx = 0; idx < 4; idx++) b[idx] = 0;

    task automatic tk(output logic x); x = 1; endtask
    initial tk(e);

    pullup(f);
    initial g = $random;
    unknown u(.k);
endmodule

module top;
    logic a, d, e, g, h, j, k;
    logic [3:0] b;
    wire c, f;
    m m1(.*, ._());
    assign m1.h = 1;
endmodule
)";

    CompilationOptions coptions;
    coptions.flags |= CompilationFlags::IgnoreUnknownModules;

    Compilation compilation(coptions);
    auto diags = analyzeInstanceDrivers(code, compilation);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Partially undriven output port descriptions are limited") {
    auto& code = R"(
typedef struct packed {
    logic f0, f1, f2, f3, f4, f5, f6, f7, f8, f9;
} s_t;
typedef enum logic [0:19] { A, B } ea_t;

module m(output logic [7:0] mem [4096], output logic [15:0] exact, output s_t s,
         output int i, output ea_t ea);
    for (genvar j = 0; j < 4096; j += 2) begin : g
        assign mem[j] = 0;
    end
    for (genvar j = 0; j < 16; j += 2) begin : h
        assign exact[j] = 0;
    end
    assign s.f0 = 0;
    for (genvar j = 0; j < 32; j += 2) begin : k
        assign i[j] = 0;
    end
    for (genvar j = 0; j < 20; j += 2) begin : l
        assign ea[j] = 0;
    end
endmodule
)";

    Compilation compilation;
    auto diags = analyzeInstanceDrivers(code, compilation);
    REQUIRE(diags.size() == 5);

    // Array elements.
    CHECK(undrivenArg(diags[0]) ==
          "mem[1], mem[3], mem[5], mem[7], mem[9], mem[11], mem[13], mem[15], ...");

    // Exactly at the limit is not truncated.
    CHECK(undrivenArg(diags[1]) ==
          "exact[1], exact[3], exact[5], exact[7], exact[9], exact[11], exact[13], exact[15]");

    // Struct fields.
    CHECK(undrivenArg(diags[2]) == "s.f1, s.f2, s.f3, s.f4, s.f5, s.f6, s.f7, s.f8, ...");

    // Integral bit ranges, descending and ascending; truncation keeps the lowest indices.
    CHECK(undrivenArg(diags[3]) == "i[1], i[3], i[5], i[7], i[9], i[11], i[13], i[15], ...");
    CHECK(undrivenArg(diags[4]) ==
          "ea[1], ea[3], ea[5], ea[7], ea[9], ea[11], ea[13], ea[15], ...");
}

TEST_CASE("Instance undriven port warnings are exclusive with undriven-port") {
    auto& code = R"(
module m #(parameter bit P = 0) (output logic a, output logic b);
    if (P) begin : g
        assign b = 1;
    end
endmodule

module top;
    logic a, b;
    m m1(.a, .b);
endmodule
)";

    // Port 'a' is never driven anywhere so it gets UndrivenPort,
    // while 'b' is only undriven in this instance.
    Compilation compilation;
    AnalysisOptions options;
    options.flags = AnalysisFlags::CheckUnused | AnalysisFlags::CheckInstanceDrivers;
    AnalysisManager analysisManager(options);
    Diagnostics diags;
    for (auto& diag : analyze(code, compilation, analysisManager)) {
        if (diag.code == diag::UndrivenPort || diag.code == diag::UndrivenPortInstance)
            diags.push_back(diag);
    }

    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::UndrivenPort);
    CHECK(std::get<std::string>(diags[0].args[0]) == "a");
    CHECK(diags[1].code == diag::UndrivenPortInstance);
    CHECK(std::get<std::string>(diags[1].args[0]) == "b");

    // The exclusion doesn't depend on whether the unused checks are enabled.
    Compilation compilation2;
    diags = analyzeInstanceDrivers(code, compilation2);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::UndrivenPortInstance);
    CHECK(std::get<std::string>(diags[0].args[0]) == "b");
}
