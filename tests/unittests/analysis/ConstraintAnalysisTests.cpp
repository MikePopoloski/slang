// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "AnalysisTests.h"

#include "slang/diagnostics/AnalysisDiags.h"

TEST_CASE("LRM example: no cycle -- y solved before x") {
    auto& code = R"(
class B;
    rand int x, y;
    function int F(int a); return a; endfunction
    constraint C { x <= F(y); }
    constraint D { y inside {2, 4, 8}; }
endclass

module m;
endmodule
)";
    Compilation compilation;
    AnalysisManager analysisManager;
    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Simple two-variable constraint ordering cycle") {
    // x <= F(y) -> y before x
    // y <= G(x) -> x before y
    // Cycle: y -> x -> y
    auto& code = R"(
class B;
    rand int x, y;
    function int F(int a); return a; endfunction
    function int G(int a); return a; endfunction
    constraint C { x <= F(y); }
    constraint D { y <= G(x); }
endclass

module m;
endmodule
)";
    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstraintFuncArgCycle);
}

TEST_CASE("Three-variable constraint ordering cycle") {
    auto& code = R"(
class C;
    rand int x, y, z;
    function int F(int a); return a; endfunction
    constraint C1 { x <= F(y); }
    constraint C2 { y <= F(z); }
    constraint C3 { z <= F(x); }
endclass

module m;
endmodule
)";
    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstraintFuncArgCycle);
}

TEST_CASE("No cycle with multiple variables and DAG ordering") {
    auto& code = R"(
class D;
    rand int x, y, z;
    function int F(int a); return a; endfunction
    function int G(int a); return a; endfunction
    constraint C1 { x <= F(y); }
    constraint C2 { x <= G(z); }
    constraint C3 { y == F(z); }
endclass

module m;
endmodule
)";
    Compilation compilation;
    AnalysisManager analysisManager;
    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("System function calls do not establish ordering") {
    auto& code = R"(
class E;
    rand int x, y;
    constraint C { x <= $clog2(y); }
    constraint D { y <= x + 1; }
endclass

module m;
endmodule
)";
    Compilation compilation;
    AnalysisManager analysisManager;
    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("randc variable in function arg ordering cycle") {
    auto& code = R"(
class F;
    randc int x;
    rand int y;
    function int F(int a); return a; endfunction
    function int G(int a); return a; endfunction
    constraint C { y <= F(x); }
    constraint D { x <= G(y); }
endclass

module m;
endmodule
)";
    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstraintFuncArgCycle);
}

TEST_CASE("Nested function calls still establish ordering") {
    auto& code = R"(
class G;
    rand int x, y;
    function int F(int a); return a; endfunction
    function int G2(int a); return a; endfunction
    function int H(int a); return a; endfunction
    constraint C1 { x <= F(G2(y)); }
    constraint C2 { y <= H(x); }
endclass

module m;
endmodule
)";
    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstraintFuncArgCycle);
}

TEST_CASE("Constraint ordering cycle in implication body") {
    auto& code = R"(
class I;
    rand int x, y;
    rand bit cond;
    function int F(int a, b); return a; endfunction
    constraint C1 { cond -> { (x + y) <= F(y, x); } }
endclass

module m;
endmodule
)";
    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstraintFuncArgCycle);
}

TEST_CASE("Simple solve-before cycle") {
    // solve x before y and solve y before x creates a cycle.
    auto& code = R"(
class A;
    rand int x, y;
    constraint C1 { solve x before y; }
    constraint C2 { solve y before x; }
endclass

module m;
endmodule
)";
    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstraintSolveCycle);
}

TEST_CASE("Three-variable solve-before cycle") {
    // x before y, y before z, z before x forms a cycle.
    auto& code = R"(
class B;
    rand int x, y, z;
    constraint C { solve x before y; solve y before z; solve z before x; }
endclass

module m;
endmodule
)";
    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstraintSolveCycle);
}

TEST_CASE("Solve-before DAG -- no cycle") {
    // x before y, x before z, y before z is a valid DAG.
    auto& code = R"(
class C;
    rand int x, y, z;
    constraint C { solve x before y; solve x before z; solve y before z; }
endclass

module m;
endmodule
)";
    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    CHECK_DIAGS_EMPTY;
}

TEST_CASE("Solve-before cycle across multiple constraint blocks") {
    // The cycle spans two separate constraint blocks.
    auto& code = R"(
class D;
    rand int x, y;
    constraint C1 { solve x before y; }
    constraint C2 { solve y before x; }
endclass

module m;
endmodule
)";
    Compilation compilation;
    AnalysisManager analysisManager;

    auto diags = analyze(code, compilation, analysisManager);
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstraintSolveCycle);
}
