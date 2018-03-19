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

TEST_CASE("Integer operators") {
    ScriptSession session;

#define EVAL(expr, result) CHECK_THAT(session.eval(expr).integer(), exactlyEquals(result))
    // Bit shifts
    EVAL("4 << 2", 16);
    EVAL("4 <<< 2", 16);
    EVAL("4 >> 1", 2);
    EVAL("-4 >>> 1", -2);
    EVAL("-65'sd4 >>> 1", "-65'sb10"_si);

    // Conditional operator
    EVAL("2 == 2 ? 5 : 4", 5);
    EVAL("(2 * 2) == 3 ? 5 : 4", 4);
    EVAL("'z ? 5 : 6", "32'sb1xx"_si);
    EVAL("(1 / 0) ? 128'b101 : 128'b110", "128'b1xx"_si);
    EVAL("'x ? 5 : 5", 5);

    // Literals
    EVAL("43'b10x", "43'b10x"_si);
    EVAL("22'b101x", "22'b101x"_si);
    EVAL("72'hxxffffffffffffffff", "72'hxxffffffffffffffff"_si);
    EVAL("2'b101", "2'b01"_si);

    // Literal unknown extension
    EVAL("5'bx01", "5'bxxx01"_si);
    EVAL("5'bz01", "5'bzzz01"_si);
    EVAL("68'bz0000", "68'hzzzzzzzzzzzzzzzzz0"_si);

    // Unbased unsized literals
    EVAL("1 << '1", 2);
    EVAL("'1 + 65'b0", "65'h1ffffffffffffffff"_si);

    // Concatenations
    EVAL("{2'b11, 4'b0010, 3'b101}", "9'b110010101"_si);
    EVAL("{2'b11, 3'b101}", "5'b11101"_si);
    EVAL("{22'b0, 43'b100, 1'b1 / 1'b0}", "66'b100x"_si);

    // Replications
    EVAL("{4 {2'b10}}", "8'b10101010"_si);
    EVAL("{((2 + 2) - 4 + 4) {2'b01}}", "8'b01010101"_si);
    EVAL("{2'b10, {0 {4'b1001}}, 2'b01}", "4'b1001"_si);

    // Wildcard equality
    EVAL("5'b11001 ==? {1'b1 / 1'b0, 4'b1001}", 1);
    EVAL("({1'b1 / 1'b0, 4'b1001} ==? 5'b11001) === 'x", 1);

    // Bit selects
    EVAL("3'd7[2]", 1);
    EVAL("5'd25[3:0]", 9);
    EVAL("5'd25[3:1]", 4);
    EVAL("65'h1ffffffffffffffff[64:62]", "3'b111"_si);
    EVAL("5'd25[0 +: 3]", 9);
    EVAL("5'd25[3 -: 3]", 9);

    // Weird / out of range part selects
    EVAL("4'b1001[(1 / 0)]", "1'bx"_si);
    EVAL("4'b1001[(1/ 0) +: 2]", "2'bxx"_si);
    EVAL("4'b1001[3 : -1]", "5'b1001x"_si);
    EVAL("4'b1001[4 : 1]", "4'bx100"_si);
    EVAL("4'b1001[4 : -1]", "6'bx1001x"_si);
    EVAL("4'b1001[105 : 101]", "5'bxxxxx"_si);
}

TEST_CASE("Assignments") {
    ScriptSession session;
    session.eval("struct packed { logic [2:0] a; logic b; } foo;");

    EVAL("foo = 4'b1101", 13);
    EVAL("foo.a = 3'b001", 1);
    EVAL("foo.b = 1'b0", 0);
    EVAL("foo", 2);
    EVAL("foo.a", 1);

    EVAL("foo.a[1] = 1'b1", 1);
    EVAL("foo", 6);
    EVAL("foo.a[2:0] = '0", 0);
    EVAL("foo", 0);
    EVAL("foo[0+:1] = 2'b11", 3);
    EVAL("foo", 3);
    EVAL("foo[3-:3] = 4'b1010", 10);
    EVAL("foo", 10);

    session.eval("logic [3:1][7:2] bar = '0;");
    EVAL("bar[2] = 3'b101", 5);
    EVAL("bar[2][3]", 1);
    EVAL("bar[7:6] = 6'b110011", 51);
    EVAL("bar", 208901);
}

TEST_CASE("bit select weird indices", "[eval]") {
    // The above bit select cases test the "normal" case where vectors are specified
    // with [N : 0]. Here we test "up-vectors" and non-zero lower bounds.
    ScriptSession session;
    session.eval("logic [0 : 15] up_vect = 5'b10111;");

    auto value = session.eval("up_vect[12:14]").integer();
    CHECK(value == "3'b011"_si);

    value = session.eval("up_vect[12 -: 2]").integer();
    CHECK(value == "3'b011"_si);

    value = session.eval("up_vect[14 +: 2]").integer();
    CHECK(value == "3'b011"_si);

    session.eval("logic [20 : 5] down_vect = 5'd25");

    value = session.eval("down_vect[8:5]").integer();
    CHECK(value == "4'd9"_si);

    value = session.eval("down_vect[5 +: 3]").integer();
    CHECK(value == 9);

    value = session.eval("down_vect[8 -: 3]").integer();
    CHECK(value == 9);
}

TEST_CASE("dimension based system functions", "[eval]") {
    ScriptSession session;
    session.eval("logic [0 : 15] up_vect = 5'b10111;");
    session.eval("logic [15 : 0] down_vect = 5'd25");

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

    for (int i = 0; i < 2; i++)
        session.eval("++a");
    CHECK(session.eval("a").integer() == 125);

    for (int i = 0; i < 3; i++)
        session.eval("--a");
    CHECK(session.eval("a").integer() == 122);
}