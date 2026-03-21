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
    comp.getAllDiagnostics();

    CodeGenerator gen(comp);
    for (auto unit : comp.getCompilationUnits())
        gen.emitScope(*unit);
    gen.emitExports();

    return gen;
}

TEST_CASE("jit: integer add", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        export "DPI-C" function add;
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
        export "DPI-C" function mul;
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
        export "DPI-C" function forty_two;
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
        export "DPI-C" function double_it;
        export "DPI-C" function quad;
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
        export "DPI-C" function abs_val;
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
        export "DPI-C" function fadd;
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
        export "DPI-C" function fadd;
        function automatic real fadd();
            return 1.5 + 2.6;
        endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    auto result = jitOrErr->runFunction("fadd", {});
    REQUIRE(result);
    CHECK(result->toString() == "4.1");
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
        export "DPI-C" function int_plus;
        export "DPI-C" function int_minus;
        export "DPI-C" function int_bitnot;
        export "DPI-C" function bit8_lognot;
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
        // DPI calling convention: bit [7:0] arg is passed as svBitVecVal* (uint32_t*)
        auto fn = reinterpret_cast<uint8_t (*)(uint32_t*)>(*fnOrErr);
        uint32_t v;
        v = 0x00u;
        CHECK(fn(&v) == 1); // !0 = 1
        v = 0xFFu;
        CHECK(fn(&v) == 0); // !nonzero = 0
        v = 0x01u;
        CHECK(fn(&v) == 0);
    }
}

static uint8_t make_v1(uint8_t val, uint8_t unk) {
    return static_cast<uint8_t>((unk << 1) | (val & 1));
}

TEST_CASE("jit: unary plus minus bitnot four-state", "[jit]") {
    // logic [7:0] cannot be a DPI return type, so the core functions are wrapped
    // in DPI-exported helpers that test specific cases and return bit (pass/fail).
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        function automatic logic [7:0] logic8_minus(logic [7:0] a); return -a; endfunction
        function automatic logic [7:0] logic8_bitnot(logic [7:0] a); return ~a; endfunction
        export "DPI-C" function test_logic8_minus;
        export "DPI-C" function test_logic8_bitnot;
        function automatic bit test_logic8_minus();
            if (logic8_minus(8'h00) !== 8'h00) return '0; // -0 = 0
            if (logic8_minus(8'h05) !== 8'hFB) return '0; // -5 mod 256 = 0xFB
            logic [7:0] xval = 8'bxxxxxxxx;
            if (logic8_minus(xval) !== 8'bxxxxxxxx) return '0; // all-X in -> all-X out
            return '1;
        endfunction
        function automatic bit test_logic8_bitnot();
            if (logic8_bitnot(8'h00) !== 8'hFF) return '0;
            if (logic8_bitnot(8'hFF) !== 8'h00) return '0;
            logic [7:0] mix = 8'bxxxx_1111; // upper nibble X, lower nibble 1s
            if (logic8_bitnot(mix) !== 8'bxxxx_0000) return '0; // upper stays X, lower flips
            return '1;
        endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    {
        auto fnOrErr = jitOrErr->lookup("test_logic8_minus");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)()>(*fnOrErr);
        CHECK(fn() == 1);
    }
    {
        auto fnOrErr = jitOrErr->lookup("test_logic8_bitnot");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)()>(*fnOrErr);
        CHECK(fn() == 1);
    }
}

TEST_CASE("jit: unary logical not four-state", "[jit]") {
    // DPI calling convention: logic [7:0] arg is passed as svLogicVecVal* {aval, bval}.
    // logic (scalar) arg/return is uint8_t (svLogic: 0=0, 1=1, 2=X, 3=Z).
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        export "DPI-C" function logic8_lognot;
        export "DPI-C" function logic1_lognot;
        function automatic logic logic8_lognot(logic [7:0] a); return !a; endfunction
        function automatic logic logic1_lognot(logic a); return !a; endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    constexpr uint8_t kZero = 0, kOne = 1, kX = 2;

    struct SVLogicVecVal {
        uint32_t aval, bval;
    };

    {
        auto fnOrErr = jitOrErr->lookup("logic8_lognot");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(SVLogicVecVal*)>(*fnOrErr);

        SVLogicVecVal v;
        v = {0x00u, 0x00u};
        CHECK(fn(&v) == kOne); // !0 = 1
        v = {0xFFu, 0x00u};
        CHECK(fn(&v) == kZero); // !nonzero = 0
        v = {0x01u, 0x00u};
        CHECK(fn(&v) == kZero); // !1 = 0
        // Any unknown bit -> result is X
        v = {0x00u, 0xFFu};
        CHECK(fn(&v) == kX); // all X
        v = {0xFFu, 0xFFu};
        CHECK(fn(&v) == kX); // all Z
        v = {0x00u, 0x01u};
        CHECK(fn(&v) == kX); // one unknown bit
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
        export "DPI-C" function reduce_and;
        export "DPI-C" function reduce_nand;
        export "DPI-C" function reduce_or;
        export "DPI-C" function reduce_nor;
        export "DPI-C" function reduce_xor;
        export "DPI-C" function reduce_xnor;
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
        auto fn = reinterpret_cast<uint8_t (*)(uint32_t*)>(*fnOrErr);
        uint32_t v;
        v = 0xFFu;
        CHECK(fn(&v) == 1);
        v = 0x00u;
        CHECK(fn(&v) == 0);
        v = 0xFEu;
        CHECK(fn(&v) == 0);
    }
    {
        auto fnOrErr = jitOrErr->lookup("reduce_nand");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint32_t*)>(*fnOrErr);
        uint32_t v;
        v = 0xFFu;
        CHECK(fn(&v) == 0);
        v = 0x00u;
        CHECK(fn(&v) == 1);
        v = 0xFEu;
        CHECK(fn(&v) == 1);
    }
    {
        auto fnOrErr = jitOrErr->lookup("reduce_or");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint32_t*)>(*fnOrErr);
        uint32_t v;
        v = 0x00u;
        CHECK(fn(&v) == 0);
        v = 0xFFu;
        CHECK(fn(&v) == 1);
        v = 0x01u;
        CHECK(fn(&v) == 1);
    }
    {
        auto fnOrErr = jitOrErr->lookup("reduce_nor");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint32_t*)>(*fnOrErr);
        uint32_t v;
        v = 0x00u;
        CHECK(fn(&v) == 1);
        v = 0xFFu;
        CHECK(fn(&v) == 0);
        v = 0x01u;
        CHECK(fn(&v) == 0);
    }
    {
        auto fnOrErr = jitOrErr->lookup("reduce_xor");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint32_t*)>(*fnOrErr);
        uint32_t v;
        v = 0x00u;
        CHECK(fn(&v) == 0); // even parity
        v = 0xFFu;
        CHECK(fn(&v) == 0); // 8 ones = even parity
        v = 0x01u;
        CHECK(fn(&v) == 1); // 1 one = odd parity
        v = 0x03u;
        CHECK(fn(&v) == 0); // 2 ones = even parity
    }
    {
        auto fnOrErr = jitOrErr->lookup("reduce_xnor");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(uint32_t*)>(*fnOrErr);
        uint32_t v;
        v = 0x00u;
        CHECK(fn(&v) == 1); // ~^0 = 1
        v = 0xFFu;
        CHECK(fn(&v) == 1); // 8 ones: even parity -> ~0 = 1
        v = 0x01u;
        CHECK(fn(&v) == 0); // odd parity -> ~1 = 0
        v = 0x03u;
        CHECK(fn(&v) == 1); // even parity -> ~0 = 1
    }
}

TEST_CASE("jit: unary reduction operators four-state", "[jit]") {
    Compilation comp;
    auto gen = buildCodegen(comp, R"(
        export "DPI-C" function reduce_and;
        export "DPI-C" function reduce_nand;
        export "DPI-C" function reduce_or;
        export "DPI-C" function reduce_nor;
        export "DPI-C" function reduce_xor;
        export "DPI-C" function reduce_xnor;
        function automatic logic reduce_and(logic [7:0] v); return &v; endfunction
        function automatic logic reduce_nand(logic [7:0] v); return ~&v; endfunction
        function automatic logic reduce_or(logic [7:0] v); return |v; endfunction
        function automatic logic reduce_nor(logic [7:0] v); return ~|v; endfunction
        function automatic logic reduce_xor(logic [7:0] v); return ^v; endfunction
        function automatic logic reduce_xnor(logic [7:0] v); return ~^v; endfunction
    )");

    auto jitOrErr = JIT::create(std::move(gen));
    REQUIRE(jitOrErr);

    // DPI calling convention: logic [7:0] arg is passed as svLogicVecVal* {aval, bval}.
    // logic return is uint8_t (svLogic: 0=0, 1=1, 2=X, 3=Z).
    struct SVLogicVecVal {
        uint32_t aval, bval;
    };
    SVLogicVecVal all_zeros = {0x00u, 0x00u};
    SVLogicVecVal all_ones = {0xFFu, 0x00u};
    SVLogicVecVal all_x = {0x00u, 0xFFu};
    SVLogicVecVal all_z = {0xFFu, 0xFFu};
    SVLogicVecVal zeros_x = {0x00u, 0x0Fu}; // lower nibble unknown, upper nibble 0
    SVLogicVecVal ones_x = {0xF0u, 0x0Fu};  // upper nibble 1s, lower nibble unknown
    SVLogicVecVal one_bit = {0x01u, 0x00u};
    SVLogicVecVal two_bits = {0x03u, 0x00u};

    constexpr uint8_t kZero = 0, kOne = 1, kX = 2;

    // &: 0 if any definite-zero; X if no definite-zero but some unknowns; 1 if all definitely 1.
    {
        auto fnOrErr = jitOrErr->lookup("reduce_and");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(SVLogicVecVal*)>(*fnOrErr);
        CHECK(fn(&all_zeros) == kZero);
        CHECK(fn(&all_ones) == kOne);
        CHECK(fn(&all_x) == kX);
        CHECK(fn(&all_z) == kX);      // val=1 but all unknown; not all definitely 1
        CHECK(fn(&zeros_x) == kZero); // definite zero bits dominate
        CHECK(fn(&ones_x) == kX);     // no definite zeros, has unknowns
    }
    // ~&
    {
        auto fnOrErr = jitOrErr->lookup("reduce_nand");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(SVLogicVecVal*)>(*fnOrErr);
        CHECK(fn(&all_zeros) == kOne);
        CHECK(fn(&all_ones) == kZero);
        CHECK(fn(&all_x) == kX);
        CHECK(fn(&all_z) == kX);
        CHECK(fn(&zeros_x) == kOne); // AND=0 -> NAND=1
        CHECK(fn(&ones_x) == kX);    // AND=X -> NAND=X
    }
    // |: 1 if any definite-one; X if no definite-one but some unknowns; 0 if all definitely 0.
    {
        auto fnOrErr = jitOrErr->lookup("reduce_or");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(SVLogicVecVal*)>(*fnOrErr);
        CHECK(fn(&all_zeros) == kZero);
        CHECK(fn(&all_ones) == kOne);
        CHECK(fn(&all_x) == kX);
        CHECK(fn(&all_z) == kX);    // val=1 but all unknown; no definite ones
        CHECK(fn(&ones_x) == kOne); // definite one bits dominate
        CHECK(fn(&zeros_x) == kX);  // no definite ones, has unknowns
    }
    // ~|
    {
        auto fnOrErr = jitOrErr->lookup("reduce_nor");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(SVLogicVecVal*)>(*fnOrErr);
        CHECK(fn(&all_zeros) == kOne);
        CHECK(fn(&all_ones) == kZero);
        CHECK(fn(&all_x) == kX);
        CHECK(fn(&all_z) == kX);
        CHECK(fn(&ones_x) == kZero); // OR=1 -> NOR=0
        CHECK(fn(&zeros_x) == kX);   // OR=X -> NOR=X
    }
    // ^: X if any unknown; otherwise parity of val bits.
    {
        auto fnOrErr = jitOrErr->lookup("reduce_xor");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(SVLogicVecVal*)>(*fnOrErr);
        CHECK(fn(&all_zeros) == kZero); // even parity
        CHECK(fn(&all_ones) == kZero);  // 8 ones = even parity
        CHECK(fn(&all_x) == kX);
        CHECK(fn(&all_z) == kX);
        CHECK(fn(&zeros_x) == kX);
        CHECK(fn(&ones_x) == kX);
        CHECK(fn(&one_bit) == kOne);   // odd parity
        CHECK(fn(&two_bits) == kZero); // even parity
    }
    // ~^
    {
        auto fnOrErr = jitOrErr->lookup("reduce_xnor");
        REQUIRE(fnOrErr);
        auto fn = reinterpret_cast<uint8_t (*)(SVLogicVecVal*)>(*fnOrErr);
        CHECK(fn(&all_zeros) == kOne); // ~^0 = 1
        CHECK(fn(&all_ones) == kOne);  // 8 ones: even parity -> ~0 = 1
        CHECK(fn(&all_x) == kX);
        CHECK(fn(&all_z) == kX);
        CHECK(fn(&zeros_x) == kX);
        CHECK(fn(&ones_x) == kX);
        CHECK(fn(&one_bit) == kZero); // odd parity -> ~1 = 0
        CHECK(fn(&two_bits) == kOne); // even parity -> ~0 = 1
    }
}
