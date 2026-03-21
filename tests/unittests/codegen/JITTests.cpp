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

TEST_CASE("jit: unary plus minus bitnot two-state", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic int int_plus(int a); return +a; endfunction
        function automatic int int_minus(int a); return -a; endfunction
        function automatic int int_bitnot(int a); return ~a; endfunction
        function automatic bit bit8_lognot(bit [7:0] a); return !a; endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    {
        auto fnOrErr = jitOrErr->lookup("int_plus");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<int (*)(int)>(*fnOrErr);
        CHECK(fn(5) == 5);
        CHECK(fn(-3) == -3);
        CHECK(fn(0) == 0);
    }
    {
        auto fnOrErr = jitOrErr->lookup("int_minus");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<int (*)(int)>(*fnOrErr);
        CHECK(fn(5) == -5);
        CHECK(fn(-3) == 3);
        CHECK(fn(0) == 0);
    }
    {
        auto fnOrErr = jitOrErr->lookup("int_bitnot");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<int (*)(int)>(*fnOrErr);
        CHECK(fn(0) == -1);
        CHECK(fn(-1) == 0);
        CHECK(fn(0x0F0F0F0F) == (int)0xF0F0F0F0);
    }
    {
        auto fnOrErr = jitOrErr->lookup("bit8_lognot");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint8_t)>(*fnOrErr);
        CHECK(fn(0x00) == 1); // !0 = 1
        CHECK(fn(0xFF) == 0); // !nonzero = 0
        CHECK(fn(0x01) == 0);
    }
}

static uint16_t make_v8(uint8_t val, uint8_t unk) {
    return static_cast<uint16_t>((uint16_t(unk) << 8) | val);
}

static uint8_t make_v1(uint8_t val, uint8_t unk) {
    return static_cast<uint8_t>((unk << 1) | (val & 1));
}

TEST_CASE("jit: unary plus minus bitnot four-state", "[jit]") {
    // For logic [7:0]: i16 encoding — lower byte = val bits, upper byte = unk bits.
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic logic [7:0] logic8_minus(logic [7:0] a); return -a; endfunction
        function automatic logic [7:0] logic8_bitnot(logic [7:0] a); return ~a; endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    auto get_val = [](uint16_t v) -> uint8_t { return v & 0xFF; };
    auto get_unk = [](uint16_t v) -> uint8_t { return v >> 8; };

    {
        auto fnOrErr = jitOrErr->lookup("logic8_minus");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint16_t (*)(uint16_t)>(*fnOrErr);

        auto r0 = fn(make_v8(0x00, 0x00)); // -0 = 0
        CHECK(get_val(r0) == 0x00);
        CHECK(get_unk(r0) == 0x00);

        auto r5 = fn(make_v8(0x05, 0x00)); // -5 = 251 = 0xFB
        CHECK(get_val(r5) == 0xFB);
        CHECK(get_unk(r5) == 0x00);

        // Any unknown makes result all-X
        auto rx = fn(make_v8(0x01, 0x01));
        CHECK(get_unk(rx) == 0xFF);
    }
    {
        auto fnOrErr = jitOrErr->lookup("logic8_bitnot");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint16_t (*)(uint16_t)>(*fnOrErr);

        auto r0 = fn(make_v8(0x00, 0x00)); // ~0x00 = 0xFF
        CHECK(get_val(r0) == 0xFF);
        CHECK(get_unk(r0) == 0x00);

        auto rff = fn(make_v8(0xFF, 0x00)); // ~0xFF = 0x00
        CHECK(get_val(rff) == 0x00);
        CHECK(get_unk(rff) == 0x00);

        // Unknown bits stay unknown; val bits for unknown positions become 0
        auto rx = fn(make_v8(0xF0, 0x0F));
        CHECK(get_val(rx) == 0x00);
        CHECK(get_unk(rx) == 0x0F);
    }
}

TEST_CASE("jit: unary logical not four-state", "[jit]") {
    // For logic [7:0] input: i16. Result is logic (i2): 0=def0, 1=def1, 2=X.
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic logic logic8_lognot(logic [7:0] a); return !a; endfunction
        function automatic logic logic1_lognot(logic a); return !a; endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    constexpr uint8_t kZero = 0, kOne = 1, kX = 2;

    {
        auto fnOrErr = jitOrErr->lookup("logic8_lognot");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint16_t)>(*fnOrErr);

        CHECK(fn(make_v8(0x00, 0x00)) == kOne);  // !0 = 1
        CHECK(fn(make_v8(0xFF, 0x00)) == kZero); // !nonzero = 0
        CHECK(fn(make_v8(0x01, 0x00)) == kZero); // !1 = 0
        // Any unknown bit -> result is X
        CHECK(fn(make_v8(0x00, 0xFF)) == kX); // all X
        CHECK(fn(make_v8(0xFF, 0xFF)) == kX); // all Z
        CHECK(fn(make_v8(0x00, 0x01)) == kX); // one unknown bit
    }
    {
        auto fnOrErr = jitOrErr->lookup("logic1_lognot");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint8_t)>(*fnOrErr);

        CHECK(fn(make_v1(0, 0)) == kOne);  // !0 = 1
        CHECK(fn(make_v1(1, 0)) == kZero); // !1 = 0
        CHECK(fn(make_v1(0, 1)) == kX);    // !X = X (val=0, unk=1)
        CHECK(fn(make_v1(1, 1)) == kX);    // !Z = X (val=1, unk=1)
    }
}

TEST_CASE("jit: unary reduction operators two-state", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic bit reduce_and(bit [7:0] v); return &v; endfunction
        function automatic bit reduce_nand(bit [7:0] v); return ~&v; endfunction
        function automatic bit reduce_or(bit [7:0] v); return |v; endfunction
        function automatic bit reduce_nor(bit [7:0] v); return ~|v; endfunction
        function automatic bit reduce_xor(bit [7:0] v); return ^v; endfunction
        function automatic bit reduce_xnor(bit [7:0] v); return ~^v; endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    {
        auto fnOrErr = jitOrErr->lookup("reduce_and");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint8_t)>(*fnOrErr);
        CHECK(fn(0xFF) == 1);
        CHECK(fn(0x00) == 0);
        CHECK(fn(0xFE) == 0);
    }
    {
        auto fnOrErr = jitOrErr->lookup("reduce_nand");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint8_t)>(*fnOrErr);
        CHECK(fn(0xFF) == 0);
        CHECK(fn(0x00) == 1);
        CHECK(fn(0xFE) == 1);
    }
    {
        auto fnOrErr = jitOrErr->lookup("reduce_or");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint8_t)>(*fnOrErr);
        CHECK(fn(0x00) == 0);
        CHECK(fn(0xFF) == 1);
        CHECK(fn(0x01) == 1);
    }
    {
        auto fnOrErr = jitOrErr->lookup("reduce_nor");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint8_t)>(*fnOrErr);
        CHECK(fn(0x00) == 1);
        CHECK(fn(0xFF) == 0);
        CHECK(fn(0x01) == 0);
    }
    {
        auto fnOrErr = jitOrErr->lookup("reduce_xor");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint8_t)>(*fnOrErr);
        CHECK(fn(0x00) == 0); // even parity
        CHECK(fn(0xFF) == 0); // 8 ones = even parity
        CHECK(fn(0x01) == 1); // 1 one = odd parity
        CHECK(fn(0x03) == 0); // 2 ones = even parity
    }
    {
        auto fnOrErr = jitOrErr->lookup("reduce_xnor");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint8_t)>(*fnOrErr);
        CHECK(fn(0x00) == 1); // ~^0 = 1
        CHECK(fn(0xFF) == 1); // 8 ones: even parity -> ~0 = 1
        CHECK(fn(0x01) == 0); // odd parity -> ~1 = 0
        CHECK(fn(0x03) == 1); // even parity -> ~0 = 1
    }
}

TEST_CASE("jit: unary reduction operators four-state", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic logic reduce_and(logic [7:0] v); return &v; endfunction
        function automatic logic reduce_nand(logic [7:0] v); return ~&v; endfunction
        function automatic logic reduce_or(logic [7:0] v); return |v; endfunction
        function automatic logic reduce_nor(logic [7:0] v); return ~|v; endfunction
        function automatic logic reduce_xor(logic [7:0] v); return ^v; endfunction
        function automatic logic reduce_xnor(logic [7:0] v); return ~^v; endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    const uint16_t all_zeros = make_v8(0x00, 0x00);
    const uint16_t all_ones = make_v8(0xFF, 0x00);
    const uint16_t all_x = make_v8(0x00, 0xFF);
    const uint16_t all_z = make_v8(0xFF, 0xFF);
    const uint16_t zeros_x = make_v8(0x00, 0x0F);
    const uint16_t ones_x = make_v8(0xF0, 0x0F);
    const uint16_t one_bit = make_v8(0x01, 0x00);
    const uint16_t two_bits = make_v8(0x03, 0x00);

    constexpr uint8_t kZero = 0, kOne = 1, kX = 2;

    // &: 0 if any definite-zero; X if no definite-zero but some unknowns; 1 if all definitely 1.
    {
        auto fnOrErr = jitOrErr->lookup("reduce_and");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint16_t)>(*fnOrErr);
        CHECK(fn(all_zeros) == kZero);
        CHECK(fn(all_ones) == kOne);
        CHECK(fn(all_x) == kX);
        CHECK(fn(all_z) == kX);      // val=1 but all unknown; not all definitely 1
        CHECK(fn(zeros_x) == kZero); // definite zero bits dominate
        CHECK(fn(ones_x) == kX);     // no definite zeros, has unknowns
    }
    // ~&
    {
        auto fnOrErr = jitOrErr->lookup("reduce_nand");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint16_t)>(*fnOrErr);
        CHECK(fn(all_zeros) == kOne);
        CHECK(fn(all_ones) == kZero);
        CHECK(fn(all_x) == kX);
        CHECK(fn(all_z) == kX);
        CHECK(fn(zeros_x) == kOne); // AND=0 -> NAND=1
        CHECK(fn(ones_x) == kX);    // AND=X -> NAND=X
    }
    // |: 1 if any definite-one; X if no definite-one but some unknowns; 0 if all definitely 0.
    {
        auto fnOrErr = jitOrErr->lookup("reduce_or");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint16_t)>(*fnOrErr);
        CHECK(fn(all_zeros) == kZero);
        CHECK(fn(all_ones) == kOne);
        CHECK(fn(all_x) == kX);
        CHECK(fn(all_z) == kX);    // val=1 but all unknown; no definite ones
        CHECK(fn(ones_x) == kOne); // definite one bits dominate
        CHECK(fn(zeros_x) == kX);  // no definite ones, has unknowns
    }
    // ~|
    {
        auto fnOrErr = jitOrErr->lookup("reduce_nor");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint16_t)>(*fnOrErr);
        CHECK(fn(all_zeros) == kOne);
        CHECK(fn(all_ones) == kZero);
        CHECK(fn(all_x) == kX);
        CHECK(fn(all_z) == kX);
        CHECK(fn(ones_x) == kZero); // OR=1 -> NOR=0
        CHECK(fn(zeros_x) == kX);   // OR=X -> NOR=X
    }
    // ^: X if any unknown; otherwise parity of val bits.
    {
        auto fnOrErr = jitOrErr->lookup("reduce_xor");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint16_t)>(*fnOrErr);
        CHECK(fn(all_zeros) == kZero); // even parity
        CHECK(fn(all_ones) == kZero);  // 8 ones = even parity
        CHECK(fn(all_x) == kX);
        CHECK(fn(all_z) == kX);
        CHECK(fn(zeros_x) == kX);
        CHECK(fn(ones_x) == kX);
        CHECK(fn(one_bit) == kOne);   // odd parity
        CHECK(fn(two_bits) == kZero); // even parity
    }
    // ~^
    {
        auto fnOrErr = jitOrErr->lookup("reduce_xnor");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint16_t)>(*fnOrErr);
        CHECK(fn(all_zeros) == kOne); // ~^0 = 1
        CHECK(fn(all_ones) == kOne);  // 8 ones: even parity -> ~0 = 1
        CHECK(fn(all_x) == kX);
        CHECK(fn(all_z) == kX);
        CHECK(fn(zeros_x) == kX);
        CHECK(fn(ones_x) == kX);
        CHECK(fn(one_bit) == kZero); // odd parity -> ~1 = 0
        CHECK(fn(two_bits) == kOne); // even parity -> ~0 = 1
    }
}
