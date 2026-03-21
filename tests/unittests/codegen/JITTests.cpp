// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <catch2/catch_approx.hpp>

#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/codegen/CodeGenerator.h"
#include "slang/codegen/JIT.h"

using namespace slang::codegen;

static CodeGenerator buildCodegen(Compilation& comp, std::string_view sv) {
    comp.addSyntaxTree(SyntaxTree::fromText(sv));
    CodeGenerator gen(comp);
    for (auto& member : comp.getRoot().members()) {
        if (member.kind == SymbolKind::CompilationUnit)
            gen.emitScope(member.as<CompilationUnitSymbol>());
    }
    return gen;
}

TEST_CASE("jit: integer add", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic int add(int a, int b);
            return a + b;
        endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    auto fnOrErr = jitOrErr->lookup("add");
    REQUIRE(fnOrErr);

    auto fn = reinterpret_cast<int (*)(int, int)>(*fnOrErr);
    CHECK(fn(3, 4) == 7);
    CHECK(fn(-1, 1) == 0);
    CHECK(fn(100, 200) == 300);
}

TEST_CASE("jit: integer multiply", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic int mul(int a, int b);
            return a * b;
        endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    auto fnOrErr = jitOrErr->lookup("mul");
    REQUIRE(fnOrErr);

    auto fn = reinterpret_cast<int (*)(int, int)>(*fnOrErr);
    CHECK(fn(3, 7) == 21);
    CHECK(fn(0, 99) == 0);
}

TEST_CASE("jit: return literal", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic int forty_two();
            return 42;
        endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    auto fnOrErr = jitOrErr->lookup("forty_two");
    REQUIRE(fnOrErr);

    auto fn = reinterpret_cast<int (*)()>(*fnOrErr);
    CHECK(fn() == 42);
}

TEST_CASE("jit: cross-function call", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic int double_it(int x);
            return x * 2;
        endfunction
        function automatic int quad(int x);
            return double_it(double_it(x));
        endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    auto fnOrErr = jitOrErr->lookup("quad");
    REQUIRE(fnOrErr);

    auto fn = reinterpret_cast<int (*)(int)>(*fnOrErr);
    CHECK(fn(3) == 12);
    CHECK(fn(5) == 20);
}

TEST_CASE("jit: if-else conditional", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic int abs_val(int x);
            if (x < 0)
                return -x;
            else
                return x;
        endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    auto fnOrErr = jitOrErr->lookup("abs_val");
    REQUIRE(fnOrErr);

    auto fn = reinterpret_cast<int (*)(int)>(*fnOrErr);
    CHECK(fn(5) == 5);
    CHECK(fn(-5) == 5);
    CHECK(fn(0) == 0);
}

TEST_CASE("jit: real arithmetic", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic real fadd(real a, real b);
            return a + b;
        endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    auto fnOrErr = jitOrErr->lookup("fadd");
    REQUIRE(fnOrErr);

    auto fn = reinterpret_cast<double (*)(double, double)>(*fnOrErr);
    CHECK(fn(1.5, 2.5) == Catch::Approx(4.0));
}

TEST_CASE("jit: run function helper", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic real fadd();
            return 1.5 + 2.6;
        endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    auto result = jitOrErr->runFunction("fadd");
    REQUIRE(result);
    CHECK(*result == "4.1");
}

TEST_CASE("jit: lookup unknown symbol returns error", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic int noop();
            return 0;
        endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    auto fnOrErr = jitOrErr->lookup("does_not_exist");
    CHECK_FALSE(fnOrErr);
    CHECK_FALSE(fnOrErr.error().empty());
}
