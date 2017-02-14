#include "Catch/catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

TEST_CASE("Simple eval", "[eval]") {
    ScriptSession session;
    auto value = session.eval("3 * 3");
    CHECK(value.integer() == 9);

    session.eval("int i = 4;");
    value = session.eval("i + 9");
    CHECK(value.integer() == 13);
}


TEST_CASE("Eval function calls", "[eval]") {
    ScriptSession session;
    session.eval(R"(
function logic [15:0] foo(int a, int b);
    return a + b;
endfunction
)");

    auto value = session.eval("foo(3, 4)");
    CHECK(value.integer() == 7);

    session.eval(R"(
function int bar();
    return 2;
    return 3;
endfunction
)");

    value = session.eval("bar()");
    CHECK(value.integer() == 2);
}

TEST_CASE("Nested functions", "[eval]") {
    ScriptSession session;
    session.eval(R"(
function automatic int symbols_in_data(int dataBitsPerSymbol, int data_width);
    return data_width / dataBitsPerSymbol;
endfunction
)");

    session.eval(R"(
function automatic int num_words_in_address_space(int dataBitsPerSymbol, int data_width, int address_width);
    // Riviera-PRO 2015.10 crashes when calling a function from
    // within a function. After all this is understandable since
    // this is a really hard CS problem that has never been solved
    // before... ???
    //
    int address_bits_per_word = $clog2(symbols_in_data(dataBitsPerSymbol, data_width));
    return 2**(address_width - address_bits_per_word);
endfunction
)");

    auto value = session.eval("num_words_in_address_space(8, 64, 20)");

    auto diagnostics = session.reportDiagnostics();
    if (!diagnostics.empty())
        WARN(diagnostics.c_str());

    CHECK(value.integer() == 131072);
}

TEST_CASE("Module param", "[eval]") {
    ScriptSession session;
    auto module = session.eval("module A#(parameter int P); localparam LP = P + 3; endmodule");
    CHECK(module);
    auto instance = session.eval("A #(.P(2)) a0();");
    CHECK(instance);
    auto value = session.eval("a0.LP");
    CHECK(value.integer() == 5);
}

TEST_CASE("Interface param", "[eval]") {
    ScriptSession session;
    auto interface = session.eval("interface IFACE#(parameter int W = 8); logic valid; logic [W-1:0] data; endinterface");
    CHECK(interface);
    auto instance = session.eval("IFACE #(6) i0();");
    CHECK(instance);
    auto value = session.eval("i0.W");
    CHECK(value.integer() == 6);
}

TEST_CASE("Eval if statement", "[eval]") {
    ScriptSession session;
    session.eval(R"(
function logic [15:0] foo(int a);
    if (a == 3)
        return 4;
    else
        return 5;
endfunction
)");

    auto value = session.eval("foo(3)");
    CHECK(value.integer() == 4);

    auto elseValue = session.eval("foo(2)");
    CHECK(elseValue.integer() == 5);
}

TEST_CASE("Eval for loop", "[eval]") {
    ScriptSession session;
    session.eval(R"(
function logic [15:0] foo(int a);
    logic [15:0] result = 1;
    for (int i = 0; i < a; ++i) begin
        result *= 2;
    end
    return result;
endfunction
)");

    auto value0 = session.eval("foo(0)");
    CHECK(value0.integer() == 1);

    auto value1 = session.eval("foo(1)");
    CHECK(value1.integer() == 2);

    auto value2 = session.eval("foo(2)");
    CHECK(value2.integer() == 4);

    auto value3 = session.eval("foo(3)");
    CHECK(value3.integer() == 8);
}

// Simple test wrapper, uses ==(uint64_t) to check result
#define EVAL_TEST(descr1, descr2, expr, result) \
TEST_CASE(descr1, descr2) { \
    ScriptSession session; \
    auto value = session.eval(expr).integer(); \
    CHECK(value == result); \
}

// Wrapper uses exactlyEqual and parses a text-specificied SVInt
#define EVAL_TEST_EX(descr1, descr2, expr, result) \
TEST_CASE(descr1, descr2) { \
    ScriptSession session; \
    auto value = session.eval(expr).integer(); \
    CHECK(exactlyEqual(value, SVInt(StringRef(result)))); \
}

EVAL_TEST("lshl", "[eval]", "4 << 2", 16);
EVAL_TEST("ashl", "[eval]", "4 <<< 2", 16);
EVAL_TEST("lshr", "[eval]", "4 >> 1", 2);
EVAL_TEST_EX("ashr", "[eval]", "-4 >>> 1", "-2");
EVAL_TEST_EX("ashr_long", "[eval]", "-65'sd4 >>> 1", "-65'sb10");
EVAL_TEST("conditionalT", "[eval]", "2 == 2 ? 5 : 4", 5);
EVAL_TEST("conditionalF", "[eval]", "(2 * 2) == 3 ? 5 : 4", 4);
EVAL_TEST_EX("conditionalU", "[eval]", "'z ? 5 : 6", "32'sb1xx");
EVAL_TEST_EX("conditionalU2", "[eval]", "(1 / 0) ? 128'b101 : 128'b110", "128'b1xx");
EVAL_TEST("conditionalUSame", "[eval]", "'x ? 5 : 5", 5);
EVAL_TEST("selfDeterminedUULiteral", "[eval]", "1 << '1", 2);
EVAL_TEST_EX("contextDeterminedUULiteral", "[eval]", "'1 + 65'b0", "65'h1ffffffffffffffff");
}
