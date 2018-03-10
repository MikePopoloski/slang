#include "Test.h"

#include "compilation/ScriptSession.h"

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
    int address_bits_per_word = $clog2(symbols_in_data(dataBitsPerSymbol, data_width));
    return 2**(address_width - address_bits_per_word);
endfunction
)");

    auto value = session.eval("num_words_in_address_space(8, 64, 20)");
    CHECK(value.integer() == 131072);
}
//
//TEST_CASE("Module param", "[eval]") {
//    ScriptSession session;
//    auto module = session.eval("module A#(parameter int P); localparam LP = P + 3; endmodule");
//    CHECK(module);
//    auto instance = session.eval("A #(.P(2)) a0();");
//    CHECK(instance);
//    auto value = session.eval("a0.LP");
//    CHECK(value.integer() == 5);
//}
//
//TEST_CASE("Interface param", "[eval]") {
//    ScriptSession session;
//    auto interface = session.eval("interface IFACE1#(parameter int W = 8); logic valid; logic [W-1:0] data; endinterface");
//    CHECK(interface);
//    auto instance = session.eval("IFACE1 #(6) i0();");
//    CHECK(instance);
//    auto value = session.eval("i0.W");
//    CHECK(value.integer() == 6);
//}
//
//TEST_CASE("Interface port param", "[eval]") {
//    ScriptSession session;
//    auto interface = session.eval("interface IFACE2 #(parameter int W = 8); logic valid; logic [W-1:0] data; endinterface");
//    CHECK(interface);
//    auto module = session.eval("module M(IFACE2 i); localparam int LP = i.W; endmodule");
//    CHECK(module);
//    auto port = session.eval("IFACE2 #(6) i0();");
//    CHECK(port);
//    auto instance = session.eval("M m0(i0);");
//    CHECK(instance);
//    auto value = session.eval("m0.LP");
//    CHECK(value.integer() == 6);
//}
//
//TEST_CASE("Interface array", "[eval]") {
//    ScriptSession session;
//    auto interface = session.eval("interface IFACE3 #(parameter int W = 8); logic valid; logic [W-1:0] data; endinterface");
//    CHECK(interface);
//    auto module = session.eval("module M(IFACE3 i); localparam int LP = i.W; endmodule");
//    CHECK(module);
//    auto param = session.eval("parameter int N = 1;");
//    auto port = session.eval("IFACE3 #(6) i0 [N] ();");
//    CHECK(port);
//    auto instance = session.eval("M m [] (i0);");
//    CHECK(instance);
//    auto value = session.eval("m[N-1].LP");
//    CHECK(value.integer() == 6);
//}

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
    for (int i = 0; i < a; i+=1)
        result *= 2;
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
#define EVAL_TEST(descr, expr, result) \
TEST_CASE(descr, "[eval]") { \
    ScriptSession session; \
    auto value = session.eval(expr).integer(); \
    CHECK(value == result); \
}

// Wrapper uses exactlyEqual and parses a text-specificied SVInt
#define EVAL_TEST_EX(descr, expr, result) \
TEST_CASE(descr, "[eval]") { \
    ScriptSession session; \
    auto value = session.eval(expr).integer(); \
    auto res = SVInt::fromString(result); \
    /* uncomment for diagonstics: */ \
    /* printf("%s = %s\n", value.toString(LiteralBase::Binary).c_str(), res.toString(LiteralBase::Binary).c_str()); */ \
    CHECK_THAT(value, exactlyEquals(res)); \
}

EVAL_TEST("lshl", "4 << 2", 16);
EVAL_TEST("ashl", "4 <<< 2", 16);
EVAL_TEST("lshr", "4 >> 1", 2);
EVAL_TEST_EX("ashr", "-4 >>> 1", "-2");
EVAL_TEST_EX("ashr_long", "-65'sd4 >>> 1", "-65'sb10");
EVAL_TEST("conditionalT", "2 == 2 ? 5 : 4", 5);
EVAL_TEST("conditionalF", "(2 * 2) == 3 ? 5 : 4", 4);
EVAL_TEST_EX("conditionalU", "'z ? 5 : 6", "32'sb1xx");
EVAL_TEST_EX("conditionalU2", "(1 / 0) ? 128'b101 : 128'b110", "128'b1xx");
EVAL_TEST("conditionalUSame", "'x ? 5 : 5", 5);
EVAL_TEST("selfDeterminedUULiteral", "1 << '1", 2);
EVAL_TEST_EX("contextDeterminedUULiteral", "'1 + 65'b0", "65'h1ffffffffffffffff");
EVAL_TEST_EX("concatenationLeadingZeroes", "{2'b11, 4'b0010, 3'b101}", "9'b110010101");
EVAL_TEST_EX("concatenation", "{2'b11, 3'b101}", "5'b11101");
EVAL_TEST_EX("concatenation2", "{22'b0, 43'b100, 1'b1 / 1'b0}", "66'b100x");
EVAL_TEST_EX("replicate", "{4 {2'b10}}", "8'b10101010");
EVAL_TEST_EX("nontrivialReplicate", "{((2 + 2) - 4 + 4) {2'b01}}", "8'b01010101");
EVAL_TEST_EX("concatenation with zero-width replicate", "{2'b10, {0 {4'b1001}}, 2'b01}", "4'b1001");
EVAL_TEST("wildcardEq", "5'b11001 ==? {1'b1 / 1'b0, 4'b1001}", 1);
EVAL_TEST("wildcardEqNotCommute", "({1'b1 / 1'b0, 4'b1001} ==? 5'b11001) === 'x", 1);
EVAL_TEST("bitSelect", "3'd7[2]", 1);
EVAL_TEST("bitSelectSimpleRange", "5'd25[3:0]", 9);
EVAL_TEST("bitSelectSimpleRangeNonzerobased", "5'd25[3:1]", 4);
EVAL_TEST_EX("bitSelectSimpleRangeLarge", "65'h1ffffffffffffffff[64:62]", "3'b111");
EVAL_TEST("bitSelectAscendingRange", "5'd25[0 +: 3]", 9);
EVAL_TEST("bitSelectDescendingRange", "5'd25[3 -: 3]", 9);
EVAL_TEST_EX("bitselect with unknown address", "4'b1001[(1 / 0)]", "1'bx");
EVAL_TEST_EX("rangeselect with unknown address", "4'b1001[(1/ 0) +: 2]", "2'bxx");
EVAL_TEST_EX("partially oob rangeselect (right)", "4'b1001[3 : -1]", "5'b1001x");
EVAL_TEST_EX("partially oob rangeselect (left)", "4'b1001[4 : 1]", "4'bx100");
EVAL_TEST_EX("partially oob rangeselect (both)", "4'b1001[4 : -1]", "6'bx1001x");
EVAL_TEST_EX("totally oob rangeselect", "4'b1001[105 : 101]", "5'bxxxxx");
EVAL_TEST("bits system call", "$bits(3'b101)", 3);
EVAL_TEST("bits system call 2", "$bits(23)", 32);
// Some basic tests that literals evaluate to the right values
EVAL_TEST_EX("lit", "43'b10x", "43'b10x");
EVAL_TEST_EX("lit2", "22'b101x", "22'b101x");
EVAL_TEST_EX("bigliteral with a high x", "72'hxxffffffffffffffff",
                                         "72'hxxffffffffffffffff");
EVAL_TEST_EX("literal truncation", "2'b101", "2'b01");
// If the highest bit is a z or x, that is extended to the full size
EVAL_TEST_EX("xpadding", "5'bx01", "5'bxxx01");
EVAL_TEST_EX("zpadding", "5'bz01", "5'bzzz01");
EVAL_TEST_EX("really long zpadding", "68'bz0000", "68'hzzzzzzzzzzzzzzzzz0");

TEST_CASE("bit select weird indexes", "[eval]") {
    // The above bit select cases test the "normal" case where vectors are specified
    // with [N : 0]. Here we test "up-vectors" and non-zero lower bounds.
    ScriptSession session;
    session.eval("logic [0 : 15] up_vect = 5'b10111;");

    auto value = session.eval("up_vect[12:14]").integer();
    CHECK(exactlyEqual(value, SVInt::fromString("3'b011")));

    value = session.eval("up_vect[12 -: 2]").integer();
    CHECK(exactlyEqual(value, SVInt::fromString("3'b011")));

    value = session.eval("up_vect[14 +: 2]").integer();
    CHECK(exactlyEqual(value, SVInt::fromString("3'b011")));

    session.eval("logic [20 : 5] down_vect = 5'd25");

    value = session.eval("down_vect[8:5]").integer();

    CHECK(exactlyEqual(value, SVInt::fromString("4'd9")));

    value = session.eval("down_vect[5 +: 3]").integer();
    CHECK(value == 9);

    value = session.eval("down_vect[8 -: 3]").integer();
    CHECK(value == 9);
}

TEST_CASE("dimension based system functions", "[eval]") {
    ScriptSession session;
    session.eval("logic [0 : 15] up_vect = 5'b10111;");
    session.eval("logic [15 : 0] down_vect = 5'd25");
    SVInt value;
#define EVAL(expr, result) CHECK(session.eval(expr).integer() == result)

    EVAL("$left(up_vect)", 0);
    EVAL("$right(up_vect)", 15);
    EVAL("$left(down_vect)", 15);
    EVAL("$right(down_vect)", 0);

    EVAL("$low(up_vect)", 0);
    EVAL("$high(up_vect)", 15);
    EVAL("$low(down_vect)", 0);
    EVAL("$high(down_vect)", 15);

    EVAL("$size(up_vect)", 16);
    EVAL("$size(down_vect)", 16);

    EVAL("$bits(up_vect)", 16);
    EVAL("$bits(down_vect)", 16);

    EVAL("$increment(up_vect)", -1);
    EVAL("$increment(down_vect)", 1);
#undef EVAL
}

TEST_CASE("Unary inc-dec operators", "[eval]") {
    ScriptSession session;
    session.eval("logic [7:0] a = 123;");

    CHECK(session.eval("++a").integer() == 124);
    CHECK(session.eval("--a").integer() == 123);
    CHECK(session.eval("a++").integer() == 123);
    CHECK(session.eval("a--").integer() == 124);
}