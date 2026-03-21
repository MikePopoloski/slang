// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <catch2/matchers/catch_matchers_string.hpp>

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/codegen/CodeGenerator.h"

#define CHECK_CONTAINS(var, str) CHECK_THAT(var, Catch::Matchers::ContainsSubstring(str))

using namespace slang::codegen;

static std::unique_ptr<Compilation> makeCompilation(std::string_view sv) {
    auto tree = SyntaxTree::fromText(sv);
    auto comp = std::make_unique<Compilation>();
    comp->addSyntaxTree(tree);
    return comp;
}

static std::string emitSubroutineIR(std::string_view sv) {
    auto comp = makeCompilation(sv);
    for (auto& member : comp->getRoot().members()) {
        if (member.kind != SymbolKind::CompilationUnit)
            continue;

        for (auto& inner : member.as<CompilationUnitSymbol>().membersOfType<SubroutineSymbol>()) {
            CodeGenerator ctx(*comp);
            ctx.emitSubroutine(inner);
            return ctx.getTextualIR();
        }
    }
    return {};
}

static std::string emitScopeIR(std::string_view sv) {
    auto comp = makeCompilation(sv);
    for (auto& member : comp->getRoot().members()) {
        if (member.kind == SymbolKind::CompilationUnit) {
            CodeGenerator ctx(*comp);
            ctx.emitScope(member.as<CompilationUnitSymbol>());
            return ctx.getTextualIR();
        }
    }
    return {};
}

TEST_CASE("codegen: 2-state integer add", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic int add(int a, int b);
            return a + b;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "add i32");
}

TEST_CASE("codegen: 2-state integer subtraction", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic int sub(int a, int b);
            return a - b;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "sub i32");
}

TEST_CASE("codegen: 2-state integer multiply", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic int mul(int a, int b);
            return a * b;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "mul i32");
}

TEST_CASE("codegen: return literal", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic int forty_two();
            return 42;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "forty_two");
}

TEST_CASE("codegen: real arithmetic", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic real fadd(real a, real b);
            return a + b;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "fadd double");
}

TEST_CASE("codegen: shortreal arithmetic", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic shortreal sfadd(shortreal a, shortreal b);
            return a + b;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "fadd float");
}

TEST_CASE("codegen: 4-state logic type lowered to i2", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic logic f(logic a, logic b);
            return a & b;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    // 4-state 1-bit values are encoded as i2 (val in bit 0, unk in bit 1).
    CHECK_CONTAINS(ir, "i2");
}

TEST_CASE("codegen: 4-state logic[7:0] types", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic logic [7:0] g(logic [7:0] a, logic [7:0] b);
            return a | b;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    // 4-state 8-bit values are encoded as i16 (val in [7:0], unk in [15:8]).
    CHECK_CONTAINS(ir, "i16");
}

TEST_CASE("codegen: if-else", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic int choose(int a, int b, bit sel);
            if (sel)
                return a;
            else
                return b;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "if.then");
    CHECK_CONTAINS(ir, "if.end");
}

TEST_CASE("codegen: for loop", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic int sum10();
            int s = 0;
            for (int i = 0; i < 10; i = i + 1)
                s = s + i;
            return s;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "for.cond");
    CHECK_CONTAINS(ir, "for.body");
    CHECK_CONTAINS(ir, "for.step");
}

TEST_CASE("codegen: while loop", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic int count(int n);
            int c = 0;
            while (n > 0) begin
                c = c + 1;
                n = n - 1;
            end
            return c;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "while.cond");
    CHECK_CONTAINS(ir, "while.body");
}

TEST_CASE("codegen: forever loop with break", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic int findFirst(int v);
            forever begin
                if (v == 0)
                    break;
                v = v - 1;
            end
            return v;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "forever");
    CHECK_CONTAINS(ir, "forever.exit");
}

TEST_CASE("codegen: cross-function call", "[codegen]") {
    auto ir = emitScopeIR(R"(
        function automatic int double_val(int x);
            return x * 2;
        endfunction

        function automatic int quadruple(int x);
            return double_val(double_val(x));
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "double_val");
    CHECK_CONTAINS(ir, "quadruple");
    CHECK_CONTAINS(ir, "call");
}

TEST_CASE("codegen: int to real conversion", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic real to_real(int x);
            return real'(x);
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "sitofp");
}

TEST_CASE("codegen: bit type (2-state 1-bit)", "[codegen]") {
    auto ir = emitSubroutineIR(R"(
        function automatic bit one_bit(bit a, bit b);
            return a ^ b;
        endfunction
    )");
    REQUIRE_FALSE(ir.empty());
    CHECK_CONTAINS(ir, "xor i1");
}
