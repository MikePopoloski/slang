// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"
#include <catch2/catch_approx.hpp>
#include <cmath>
using Catch::Approx;

#include "slang/ast/ScriptSession.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"

TEST_CASE("Simple eval") {
    ScriptSession session;
    auto value = session.eval("3 * 3");
    CHECK(value.integer() == 9);

    session.eval("int i = 4;");
    value = session.eval("i + 9");
    CHECK(value.integer() == 13);

    NO_SESSION_ERRORS;
}

TEST_CASE("Eval function calls") {
    ScriptSession session;
    session.eval(R"(
function logic [15:0] foo(int a, int b);
    return 16'($unsigned(a + b));
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
    NO_SESSION_ERRORS;
}

TEST_CASE("Nested functions") {
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
    NO_SESSION_ERRORS;
}

TEST_CASE("Module param") {
    ScriptSession session;
    session.eval("module A#(parameter int P); localparam LP = P + 3; endmodule");
    session.eval("A #(.P(2)) a0();");
    auto value = session.eval("a0.LP");
    CHECK(value.integer() == 5);
    NO_SESSION_ERRORS;
}

TEST_CASE("Interface param") {
    ScriptSession session;
    session.eval(
        "interface IFACE1#(parameter int W = 8); logic valid; logic [W-1:0] data; endinterface");
    session.eval("IFACE1 #(6) i0();");
    auto value = session.eval("i0.W");
    CHECK(value.integer() == 6);
    NO_SESSION_ERRORS;
}

TEST_CASE("Interface port param eval") {
    ScriptSession session;
    session.eval(R"(
interface IFACE2 #(parameter int W = 8);
    logic valid;
    logic [W-1:0] data;
endinterface
)");

    session.eval("module M(IFACE2 i); localparam int LP = i.W; endmodule");
    session.eval("IFACE2 #(6) i0();");
    session.eval("M m0(i0);");

    auto value = session.eval("m0.LP");
    CHECK(value.integer() == 6);
    NO_SESSION_ERRORS;
}

TEST_CASE("Interface array") {
    ScriptSession session;
    session.eval(R"(
interface IFACE3 #(parameter int W = 8);
    logic valid;
    logic [W-1:0] data;
endinterface
)");

    session.eval("module M(IFACE3 i); localparam int LP = i.W; endmodule");
    session.eval("parameter int N = 1;");
    session.eval("IFACE3 #(6) i0 [N] ();");
    session.eval("M m [N] (i0);");

    auto value = session.eval("m[N-1].LP");
    CHECK(value.integer() == 6);
    NO_SESSION_ERRORS;
}

TEST_CASE("Eval if statement") {
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
    NO_SESSION_ERRORS;

    SECTION("None if match") {
        ScriptSession session;
        session.eval(R"(
function logic [15:0] foo(int a);
    unique if (a == 3)
        return 4;
    else if (a < 4)
        return 5;
endfunction
)");
        auto value = session.eval("foo(10)");
        auto diags = session.getDiagnostics();
        REQUIRE(diags.size() == 1);
        CHECK(diags[0].code == diag::ConstEvalNoIfItemsMatched);
    }

    SECTION("Not unique if match") {
        ScriptSession session;
        session.eval(R"(
function logic [15:0] foo(int a);
    unique if (a == 3)
        return 4;
    else if (a < 4)
        return 5;
endfunction
)");
        auto value = session.eval("foo(3)");
        auto diags = session.getDiagnostics();
        REQUIRE(diags.size() == 1);
        CHECK(diags[0].code == diag::ConstEvalIfItemsNotUnique);
    }
}

TEST_CASE("Eval for loop") {
    ScriptSession session;
    session.eval(R"(
function automatic logic [15:0] foo(int a);
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
    NO_SESSION_ERRORS;
}

TEST_CASE("Eval nested for loop") {
    ScriptSession session;
    session.eval(R"(
typedef logic[15:0] result_t;
function automatic result_t foo(int a);
    result_t result = 1;
    int temp = 0;
    for (int i = 0; i < a; i+=1) begin
        temp = i * 2;
        for (int j = temp + 1; j < 10; j++)
            result += result_t'(j);
    end
    return result;
endfunction
)");

    auto value1 = session.eval("foo(2)");
    CHECK(value1.integer() == 88);
    NO_SESSION_ERRORS;
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

#undef EVAL
    NO_SESSION_ERRORS;
}

TEST_CASE("Real operators") {
    ScriptSession session;
    session.eval("real r = 3.14;");

    using namespace Catch::literals;
#define EVAL(expr, result) CHECK(session.eval(expr).real() == (result))
    EVAL("+r", 3.14_a);
    EVAL("-r", -3.14_a);
    EVAL("++r", 4.14_a);
    EVAL("r++", 4.14_a);
    EVAL("--r", 4.14_a);
    EVAL("r--", 4.14_a);
    EVAL("2.01 + r", 5.15_a);
    EVAL("r - 6.14", -3.0_a);
    EVAL("r * 2.2", 6.908_a);
    EVAL("r / 3.14", 1.0_a);
    EVAL("1.1 ** 2.2", 1.23328630055_a);
    EVAL("9 ** 0.5", 3.0);
    EVAL("9.0 ** (1/2)", 1.0);
    EVAL("-3.0 ** 2.0", 9.0);
#undef EVAL

#define EVAL(expr, result) CHECK(session.eval(expr).integer() == (result))
    EVAL("!r", 0);
    EVAL("r || 0", 1);
    EVAL("r && 0", 0);
    EVAL("r -> 0.0", 0);
    EVAL("r <-> 1.0", 1);
    EVAL("r > 2.9999", 1);
    EVAL("r < 3.14", 0);
    EVAL("r <= 3.15", 1);
    EVAL("r >= 0", 1);
    EVAL("3.14 == 3.14", 1);
    EVAL("3.14 != 3.14", 0);

#undef EVAL

    NO_SESSION_ERRORS;
}

TEST_CASE("Operator short circuiting") {
    ScriptSession session;
    session.eval("int a = 2, b = 3;");

#define EVAL(expr, result) CHECK(session.eval(expr).integer() == (result))

    session.eval("1 || b++");
    EVAL("b", 3);

    session.eval("0 && b++");
    EVAL("b", 3);

    session.eval("0 -> b++");
    EVAL("b", 3);

    session.eval("0 || b++");
    EVAL("b", 4);

    session.eval("1 && b++");
    EVAL("b", 5);

    session.eval("1 -> b++");
    EVAL("b", 6);

    session.eval("0 ? b++ : b");
    EVAL("b", 6);

    session.eval("1 ? b : b++");
    EVAL("b", 6);

    session.eval("'x ? a++ : b++");
    EVAL("a", 3);
    EVAL("b", 7);

#undef EVAL
    NO_SESSION_ERRORS;
}

TEST_CASE("Assignments") {
    ScriptSession session;
    session.eval("struct packed { logic [2:0] a; logic b; } foo;");

#define EVAL(expr, result) CHECK_THAT(session.eval(expr).integer(), exactlyEquals(result))
    EVAL("foo = 4'b1101", 13);
    EVAL("foo.a = 3'b001", 1);
    EVAL("foo.b = 1'b0", 0);
    EVAL("foo", 2);
    EVAL("foo.a", 1);

    EVAL("foo.a[1] = 1'b1", 1);
    EVAL("foo", 6);
    EVAL("foo.a[2:0] = '0", 0);
    EVAL("foo", 0);
    EVAL("foo[0+:2] = 2'b11", 3);
    EVAL("foo", 3);
    EVAL("foo[3-:4] = 4'b1010", 10);
    EVAL("foo", 10);

    session.eval("logic [7:2][3:1] bar = '0;");
    EVAL("bar[2] = 3'b101", 5);
    EVAL("bar[2][3]", 1);
    EVAL("bar[7:6] = 6'b110011", 51);
    EVAL("bar", 208901);

    NO_SESSION_ERRORS;
}

TEST_CASE("bit select weird indices") {
    // The above bit select cases test the "normal" case where vectors are specified
    // with [N : 0]. Here we test "up-vectors" and non-zero lower bounds.
    ScriptSession session;
    session.eval("logic [0 : 15] up_vect = 5'b10111;");

    auto value = session.eval("up_vect[12:14]").integer();
    CHECK(value == "3'b011"_si);

    value = session.eval("up_vect[12 +: 3]").integer();
    CHECK(value == "3'b011"_si);

    value = session.eval("up_vect[14 -: 3]").integer();
    CHECK(value == "3'b011"_si);

    session.eval("logic [20 : 5] down_vect = 5'd25;");

    value = session.eval("down_vect[8:5]").integer();
    CHECK(value == "4'd9"_si);

    value = session.eval("down_vect[5 +: 4]").integer();
    CHECK(value == 9);

    value = session.eval("down_vect[8 -: 4]").integer();
    CHECK(value == 9);

    NO_SESSION_ERRORS;
}

TEST_CASE("Unary inc-dec operators") {
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

    NO_SESSION_ERRORS;
}

TEST_CASE("Constant eval errors") {
    ScriptSession session;
    session.eval("logic f = 1;");
    session.eval("function int foo(int a); return int'(f) + a; endfunction");
    session.eval("function int bar(int b); return foo(b + 1); endfunction");

    CHECK(!session.eval("localparam int p = bar(1);"));

    std::string msg = "\n" + report(session.getDiagnostics());
    CHECK(msg == R"(
source:1:38: error: all identifiers that are not parameters or enums must be declared locally to a constant function
function int foo(int a); return int'(f) + a; endfunction
                                     ^
source:1:33: note: in call to 'foo(2)'
function int bar(int b); return foo(b + 1); endfunction
                                ^
source:1:20: note: in call to 'bar(1)'
localparam int p = bar(1);
                   ^
source:1:7: note: declared here
logic f = 1;
      ^
)");
}

TEST_CASE("Unpacked array eval") {
    ScriptSession session;
    session.eval("int arr[8];");
    session.eval("arr[0] = 42;");
    CHECK(session.eval("arr[0]").integer() == 42);

    session.eval("int arr2[2];");
    session.eval("arr2[0] = 1234;");
    session.eval("arr2[1] = 19;");
    session.eval("arr[1:2] = arr2;");

    session.eval("int arr3[1:0];");
    session.eval("arr3[0] = 1234;");
    session.eval("arr3[1] = 19;");

    session.eval("int sameArr[2] = '{1234, 19};");
    session.eval("int sameArr2[1:0] = '{1234, 19};");
    CHECK(session.eval("arr2 == sameArr").integer() == 1);
    CHECK(session.eval("arr2 == sameArr2").integer() == 1);
    CHECK(session.eval("arr2 == arr3").integer() == 0);

    auto cv = session.eval("arr");
    CHECK(cv.elements()[0].integer() == 42);
    CHECK(cv.elements()[1].integer() == 1234);
    CHECK(cv.elements()[2].integer() == 19);

    cv = session.eval("arr3");
    CHECK(cv.elements()[1].integer() == 1234);
    CHECK(cv.elements()[0].integer() == 19);

    CHECK(session.eval("arr[1:2] == arr2").integer() == 1);

    cv = session.eval("1 ? arr[1:2] : arr2");
    CHECK(cv.elements()[0].integer() == 1234);
    CHECK(cv.elements()[1].integer() == 19);

    cv = session.eval("'x ? arr[1:2] : arr2");
    CHECK(cv.elements()[0].integer() == 1234);
    CHECK(cv.elements()[1].integer() == 19);

    session.eval("arr2[0] = 1;");
    cv = session.eval("'x ? arr[1:2] : arr2");
    CHECK(cv.elements()[0].integer() == 0);
    CHECK(cv.elements()[1].integer() == 19);

    session.eval("arr2[0] = 142;");
    CHECK(session.eval("arr2.xor").integer() == 157);

    session.eval("arr2[1] = 63;");
    CHECK(session.eval("arr2.or").integer() == 191);
    CHECK(session.eval("arr2.and").integer() == 14);

    session.eval("arr = {sameArr2, 32, 4'd2, arr3, -9, -10}");
    CHECK(session.eval("arr[5]").integer() == 1234);

    NO_SESSION_ERRORS;
}

TEST_CASE("Dynamic array eval") {
    ScriptSession session;
    session.eval("int arr[] = '{1, 2, 3, 4};");
    session.eval("arr[0] = 42;");
    CHECK(session.eval("arr[0]").integer() == 42);
    CHECK(session.eval("arr[3]").integer() == 4);

    session.eval("int arr2[2];");
    session.eval("arr2[0] = 1234;");
    session.eval("arr2[1] = 19;");
    session.eval("arr[1:2] = arr2;");

    auto cv = session.eval("arr");
    CHECK(cv.elements()[0].integer() == 42);
    CHECK(cv.elements()[1].integer() == 1234);
    CHECK(cv.elements()[2].integer() == 19);
    CHECK(cv.elements()[3].integer() == 4);

    CHECK(session.eval("arr[1:2] == arr2").integer() == 1);

    session.eval("int arr3[] = '{5, 6, 7};");
    cv = session.eval("0 ? arr : arr3");
    CHECK(cv.elements()[0].integer() == 5);
    CHECK(cv.elements()[1].integer() == 6);

    CHECK(session.eval("arr == arr3").integer() == 0);

    cv = session.eval("'x ? arr : arr3");
    CHECK(cv.elements().empty());

    session.eval("arr3 = '{42, 1, 3, 4};");
    cv = session.eval("'x ? arr3 : arr");
    CHECK(cv.elements()[0].integer() == 42);
    CHECK(cv.elements()[1].integer() == 0);
    CHECK(cv.elements()[2].integer() == 0);
    CHECK(cv.elements()[3].integer() == 4);

    CHECK(session.eval("arr.xor").integer() == 1263);
    CHECK(session.eval("arr.or").integer() == 1279);

    session.eval("arr[3] = 42;");
    CHECK(session.eval("arr.and").integer() == 2);

    CHECK(session.eval("arr.size").integer() == 4);

    cv = session.eval("arr = new [5] (arr2);");
    REQUIRE(cv.elements().size() == 5);
    CHECK(cv.elements()[0].integer() == 1234);
    CHECK(cv.elements()[1].integer() == 19);
    CHECK(cv.elements()[2].integer() == 0);

    CHECK(session.eval("arr.size()").integer() == 5);
    session.eval("arr.delete");
    CHECK(session.eval("arr.size()").integer() == 0);

    CHECK(session.eval("arr.xor").integer() == 0);

    session.eval("arr = {}");
    CHECK(session.eval("arr.size").integer() == 0);

    session.eval("arr = {1, 2, arr2}");
    CHECK(session.eval("arr.size").integer() == 4);

    NO_SESSION_ERRORS;
}

TEST_CASE("Dynamic arrays -- out of bounds") {
    // Out of bounds accesses
    ScriptSession session;
    session.eval("int arr[] = '{1, 2, 3, 4};");

    CHECK(session.eval("arr[-1]").integer() == 0);
    session.eval("arr[-1] = 42;");
    session.eval("arr[-1:1] = '{8,9,10};");

    auto cv = session.eval("arr[-1:2]");
    CHECK(cv.elements().size() == 4);
    CHECK(cv.elements()[0].integer() == 0);
    CHECK(cv.elements()[1].integer() == 9);
    CHECK(cv.elements()[2].integer() == 10);
    CHECK(cv.elements()[3].integer() == 3);

    // Reversed queue selection results in a warning
    session.eval("int q[$] = '{1, 2, 3, 4};");
    cv = session.eval("q[1:0]");
    CHECK(cv.queue()->empty());

    // Pop from empty queue
    session.eval("for (int i = 0; i < 4; i++) void'(q.pop_front());");
    CHECK(session.eval("q.pop_back()").integer() == 0);

    auto diags = session.getDiagnostics();
    REQUIRE(diags.size() == 6);
    CHECK(diags[0].code == diag::ConstEvalDynamicArrayIndex);
    CHECK(diags[1].code == diag::ConstEvalDynamicArrayIndex);
    CHECK(diags[2].code == diag::ConstEvalDynamicArrayRange);
    CHECK(diags[3].code == diag::ConstEvalDynamicArrayRange);
    CHECK(diags[4].code == diag::ConstEvalQueueRange);
    CHECK(diags[5].code == diag::ConstEvalEmptyQueue);
}

TEST_CASE("Associative array eval") {
    ScriptSession session;
    session.eval("integer arr[string] = '{\"Hello\":4, \"World\":8, default:-1};");

    auto cv = session.eval("arr");
    auto& map = *cv.map();
    CHECK(map.size() == 2);

    auto it = map.begin();
    CHECK(it->first.str() == "Hello");
    CHECK(it->second.integer() == 4);
    it++;
    CHECK(it->first.str() == "World");
    CHECK(it->second.integer() == 8);

    CHECK(map.defaultValue.integer() == -1);

    session.eval("integer arr2[string] = arr;");
    CHECK(session.eval("arr2") == cv);

    CHECK(session.eval("4 inside { arr2 }").integer() == 1);
    CHECK(session.eval("-1 inside { arr2 }").integer() == 0);
    CHECK(session.eval("arr == arr2").integer() == 1);

    cv = session.eval("'x ? arr : arr2");
    CHECK(cv.map()->empty());

    session.eval("arr[\"bye\"] += 20;");
    CHECK(session.eval("arr[\"bye\"]").integer() == 19);
    CHECK(session.eval("arr[\"foo\"]").integer() == -1);
    CHECK(session.eval("arr[\"World\"]").integer() == 8);

    CHECK(session.eval("arr.size").integer() == 3);
    CHECK(session.eval("arr.num").integer() == 3);

    CHECK(session.eval("arr.exists(\"bye\")").integer() == 1);
    CHECK(session.eval("arr.exists(\"byebye\")").integer() == 0);

    CHECK(session.eval("arr.or").integer() == 31);

    session.eval("arr.delete(\"foo\")");
    CHECK(session.eval("arr.size").integer() == 3);

    session.eval("arr.delete(\"bye\")");
    CHECK(session.eval("arr.size").integer() == 2);

    session.eval("arr.delete");
    CHECK(session.eval("arr.size").integer() == 0);
    cv = session.eval("arr");
    CHECK(cv.map()->empty());

    CHECK(session.eval("arr.or").integer() == 0);

    session.eval(R"(
function int func(logic [31:0] i, integer arr[string]);
    case (i) inside
        [5'd1:5'd2]: return 1;
        arr: return 2;
    endcase
    return 3;
endfunction
)");
    CHECK(session.eval("func(4, arr2)").integer() == 2);

    NO_SESSION_ERRORS;
}

TEST_CASE("Queue eval") {
    ScriptSession session;
    session.eval("int arr[$] = '{1, 2, 3, 4};");
    session.eval("arr[0] = 42;");
    CHECK(session.eval("arr[0]").integer() == 42);
    CHECK(session.eval("arr[3]").integer() == 4);

    session.eval("int arr2[2];");
    session.eval("arr2[0] = 1234;");
    session.eval("arr2[1] = 19;");
    session.eval("arr[1:2] = arr2;");

    auto cv = session.eval("arr");
    CHECK(cv.queue()->at(0).integer() == 42);
    CHECK(cv.queue()->at(1).integer() == 1234);
    CHECK(cv.queue()->at(2).integer() == 19);
    CHECK(cv.queue()->at(3).integer() == 4);

    session.eval("int queueArr2[$] = arr2;");
    CHECK(session.eval("arr[1:2] == queueArr2").integer() == 1);

    session.eval("int arr3[$] = '{5, 6, 7};");
    cv = session.eval("0 ? arr : arr3");
    CHECK(cv.queue()->at(0).integer() == 5);
    CHECK(cv.queue()->at(1).integer() == 6);

    CHECK(session.eval("arr == arr3").integer() == 0);

    cv = session.eval("'x ? arr : arr3");
    CHECK(cv.queue()->empty());

    session.eval("arr3 = '{42, 1, 3, 4};");
    cv = session.eval("'x ? arr3 : arr");
    CHECK(cv.queue()->at(0).integer() == 42);
    CHECK(cv.queue()->at(1).integer() == 0);
    CHECK(cv.queue()->at(2).integer() == 0);
    CHECK(cv.queue()->at(3).integer() == 4);

    CHECK(session.eval("arr.xor").integer() == 1263);
    CHECK(session.eval("arr.or").integer() == 1279);

    session.eval("arr[3] = 42;");
    CHECK(session.eval("arr.and").integer() == 2);

    CHECK(session.eval("arr.size").integer() == 4);
    session.eval("arr[4] = 22;");
    CHECK(session.eval("arr.size").integer() == 5);
    CHECK(session.eval("$size(arr)").integer() == 5);

    session.eval(R"(
function int func(int unsigned i, int arr[$]);
    case (i) inside
        [5'd1:5'd2]: return 1;
        arr: return 2;
    endcase
    return 3;
endfunction
)");
    CHECK(session.eval("func(22, arr)").integer() == 2);

    session.eval("int empty[$];");
    CHECK(session.eval("empty.and").integer() == 0);

    session.eval("empty.push_back(5);");
    session.eval("empty.push_back(6);");
    session.eval("empty.push_front(9);");
    session.eval("empty.insert(2, 12);");
    cv = session.eval("empty");
    REQUIRE(cv.queue()->size() == 4);
    CHECK((*cv.queue())[0].integer() == 9);
    CHECK((*cv.queue())[1].integer() == 5);
    CHECK((*cv.queue())[2].integer() == 12);
    CHECK((*cv.queue())[3].integer() == 6);

    session.eval("empty.delete(1)");
    CHECK(session.eval("empty.pop_back()").integer() == 6);
    CHECK(session.eval("empty.pop_front()").integer() == 9);
    cv = session.eval("empty");
    REQUIRE(cv.queue()->size() == 1);
    CHECK((*cv.queue())[0].integer() == 12);

    session.eval("empty.delete");
    CHECK(session.eval("empty.size").integer() == 0);

    session.eval("empty = {arr, arr2, 5, 3.4}");
    CHECK(session.eval("empty.size").integer() == 9);
    CHECK(session.eval("empty[4]").integer() == 22);
    CHECK(session.eval("empty[8]").integer() == 3);

    NO_SESSION_ERRORS;
}

TEST_CASE("Unpacked struct eval") {
    ScriptSession session;
    session.eval("struct { integer a[2:0]; bit b; } foo;");
    session.eval("foo.a[0] = 42;");
    session.eval("foo.b = 1;");

    auto cv = session.eval("foo");
    CHECK(cv.elements()[0].elements()[2].integer() == 42);

    CHECK(session.eval("foo.a[0] == 42").integer() == 1);
    CHECK_THAT(session.eval("foo == foo").integer(), exactlyEquals(SVInt(logic_t::x)));
    CHECK(session.eval("foo === foo").integer() == 1);

    session.eval("var type(foo) bar;");
    CHECK(session.eval("foo === bar").integer() == 0);
    CHECK(session.eval("(1 ? foo : bar) === foo").integer() == 1);
    CHECK(session.eval("('x ? foo : bar) === bar").integer() == 1);

    NO_SESSION_ERRORS;
}

TEST_CASE("Unpacked union eval") {
    ScriptSession session;
    session.eval("union { integer a[2:0]; bit b; } foo, bar;");
    session.eval("foo.a[0] = 42;");
    session.eval("foo.b = 1;");

    CHECK(session.eval("foo").toString() == "(1) 1'b1");

    session.eval("foo.a[0] = 42;");
    session.eval("foo.a[2:1] = '{3,4};");
    CHECK(session.eval("foo").toString() == "(0) [3,4,42]");

    session.eval("bar = foo;");
    CHECK(session.eval("bar").toString() == "(0) [3,4,42]");

    // Accessing wrong member just gets you the default.
    CHECK(session.eval("foo.b").integer() == 0);

    // Inspecting common initial sequence across values is allowed.
    session.eval(R"(
union {
    struct {
        int s1;
        struct {
            int n1;
            real n2;
        } s2;
    } a;
    struct {
        struct {
            int v;
        } s1;
        int s2;
        int s3;
    } b;
    int c;
} baz;
)");

    session.eval("baz.a = '{42, '{55, 3.14}};");
    CHECK(session.eval("baz.a.s1").integer() == 42);
    CHECK(session.eval("baz.b.s1.v").integer() == 42);
    CHECK(session.eval("baz.b.s2").integer() == 55);
    CHECK(session.eval("baz.b.s3").integer() == 0);
    CHECK(session.eval("baz.c").integer() == 42);

    session.eval("baz.b = '{'{1}, 2, 3};");
    CHECK(session.eval("baz.a.s1").integer() == 1);
    CHECK(session.eval("baz.a.s2.n1").integer() == 2);
    CHECK(session.eval("baz.a.s2.n2").real() == 0.0);
    CHECK(session.eval("baz.c").integer() == 1);

    session.eval("baz.c = 123;");
    CHECK(session.eval("baz.a.s1").integer() == 123);

    CHECK(session.eval("foo == bar").integer() == 1);
    CHECK(session.eval("1 ? foo : bar").toString() == "(0) [3,4,42]");

    NO_SESSION_ERRORS;
}

TEST_CASE("String literal ops") {
    ScriptSession session;
    session.eval("bit [8*14:1] str;");

    SVInt v = session.eval("str = \"Hello world\";").integer();
    CHECK(v == "112'h48656c6c6f20776f726c64"_si);

    v = session.eval("str = 112'({str, \"!!!\"});").integer();
    CHECK(v == "112'h48656c6c6f20776f726c64212121"_si);

    session.eval("bit [8*10:1] s1, s2;");
    session.eval("s1 = \"Hello\";");
    session.eval("s2 = \" world!\";");

    // Comparison fails because of zero padding
    v = session.eval("{s1,s2} == \"Hello world!\"").integer();
    CHECK(v == 0);

    // Make the comparison succeed
    v = session.eval("{s1[5*8:1], s2[7*8:1]} == \"Hello world!\"").integer();
    CHECK(v == 1);

    // Multi-dimensional packed array
    session.eval("bit [0:11] [7:0] str2 = \"Hello world\\n\";");
    CHECK(session.eval("str2[0] == \"H\"").integer() == 1);
    CHECK(session.eval("str2[11] == 8'hA").integer() == 1);

    // Unpacked array cast
    session.eval("typedef byte asdf_t[];");
    auto elems = session.eval("asdf_t'(\"asdf\")").elements();
    REQUIRE(elems.size() == 4);

    NO_SESSION_ERRORS;
}

TEST_CASE("Dynamic string ops") {
    ScriptSession session;
    session.eval("string str1;");
    session.eval("string str2 = \"asdf\";");

    auto v = session.eval("str2").str();
    CHECK(v == "asdf");

    v = session.eval("str2 = \"Hello\\0World\\0\";").str();
    CHECK(v == "HelloWorld");

    session.eval("bit [19:0] b = 20'haxx41;");
    v = session.eval("str2 = string'(b);").str();
    CHECK(v == "\nA");

    CHECK(session.eval("str1 == str2").integer() == 0);
    CHECK(session.eval("str2 == str2").integer() == 1);
    CHECK(session.eval("str1 != str2").integer() == 1);

    CHECK(session.eval("str1 == \"\"").integer() == 1);
    CHECK(session.eval("\"\\nA\" == str2").integer() == 1);

    CHECK(session.eval("str1 <= str1").integer() == 1);
    CHECK(session.eval("str1 < str2").integer() == 1);
    CHECK(session.eval("\"aaaaa\" >= str2").integer() == 1);
    CHECK(session.eval("str2 >= \"aaaaa\"").integer() == 0);
    CHECK(session.eval("str2 > str2").integer() == 0);

    CHECK(session.eval("str2[0]").integer() == '\n');
    CHECK(session.eval("str2[0] == \"\\n\"").integer() == 1);

    session.eval("str2[0] = \"\\0\"");
    CHECK(session.eval("str2[0]").integer() == '\n');

    session.eval("str2[0] = \"aaB\"");
    CHECK(session.eval("str2[0]").integer() == 'B');

    CHECK(session.eval("1 ? str2 : str1").str() == "BA");
    CHECK(session.eval("1 ? \"C\" : str1").str() == "C");
    CHECK(session.eval("0 ? str2 : \"D\"").str() == "D");
    CHECK(session.eval("'x ? str2 : str1").str() == "");

    session.eval("integer i = 5;");
    CHECK(session.eval("str1 = {5{\"Hi\"}}").str() == "HiHiHiHiHi");
    CHECK(session.eval("str2 = {i{\"Hi\"}}").str() == "HiHiHiHiHi");

    session.eval("str1 = \"a\";");
    CHECK(session.eval("str2 = {i{str1}}").str() == "aaaaa");
    CHECK(session.eval("{str1,str2}").str() == "aaaaaa");
    CHECK(session.eval("{\"Hi\",str2}").str() == "Hiaaaaa");
    CHECK(session.eval("str2 = {\"Hi\", \"Bye\"}").str() == "HiBye");

    CHECK(session.eval("str1").str() == "a");

    session.eval("byte ba[] = \"asdf\";");
    CHECK(session.eval("string'(ba)").str() == "asdf");

    session.eval("typedef byte asdf_t[];");
    CHECK(session.eval("asdf_t'(str1)").elements().size() == 1);

    CHECK(session.eval("int'(str2)").integer() == 0x69427965);

    auto diags = session.getDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstantConversion);
}

TEST_CASE("Ambiguous numeric literals") {
    ScriptSession session;
    CHECK(session.eval("3e+2").real() == 3e2);
    CHECK(session.eval("3e2").real() == 3e2);
    CHECK(session.eval("'h 3e+2").integer() == 64);
    CHECK(session.eval("'h 3e2").integer() == 994);

    // This check is intended to hit a buffer wraparound case in ParserBase::Window::insertHead
    CHECK(session.eval("1+1+1+1+1+1+1+1+1+1+1+1+1+1+'d1+ 'h 3e+2").integer() == 79);

    NO_SESSION_ERRORS;
}

TEST_CASE("Eval case statements") {
    ScriptSession session;
    session.eval(R"(
function logic func1(string foo);
    unique case (foo)
        "bar", "foo", "foo": return 1;
        "baz": ;
        "foo": ; // error
    endcase
    return 0;
endfunction
)");
    CHECK(session.eval("func1(\"foo\")").integer() == 1);
    CHECK(session.eval("func1(\"blah\")").integer() == 0);

    session.eval(R"(
function logic func2(real foo);
    priority case (foo)
        3.4: return 1;
        2.1: ;
        3.4: ;
    endcase
    return 0;
endfunction
)");
    CHECK(session.eval("func2(3.4)").integer() == 1);
    CHECK(session.eval("func2(3.5)").integer() == 0);

    session.eval(R"(
function int func3(shortreal foo);
    case (foo)
        shortreal'(3.4): return 2;
        default: return 3;
    endcase
    return 5;
endfunction
)");
    CHECK(session.eval("func3(3.4)").integer() == 2);
    CHECK(session.eval("func3(3.5)").integer() == 3);

    session.eval(R"(
function int func4(int foo);
    unique0 case (foo)
        1,2,3: return 2;
    endcase
    return 5;
endfunction
)");
    CHECK(session.eval("func4(3)").integer() == 2);
    CHECK(session.eval("func4(6)").integer() == 5);

    session.eval(R"(
function int func5(logic [3:0] foo);
    casez (foo)
        4'b11?1: return 1;
        4'b1?11: return 2;
    endcase
    return 3;
endfunction
)");
    CHECK(session.eval("func5(4'b1011)").integer() == 2);
    CHECK(session.eval("func5(4'b1111)").integer() == 1);

    session.eval(R"(
function int func6(logic [3:0] foo);
    casex (foo)
        4'b1x?1: return 1;
        4'b1?10: return 2;
    endcase
    return 3;
endfunction
)");
    CHECK(session.eval("func6(4'b1011)").integer() == 1);
    CHECK(session.eval("func6(4'bx110)").integer() == 2);

    session.eval(R"(
function int func7;
    casex (foo)
        1: return 1;
    endcase
    return 2;
endfunction
)");
    session.eval("func7()");

    session.eval("int foo = 0;");
    session.eval(R"(
function int func8;
    casex (1)
        foo: return 1;
    endcase
    return 2;
endfunction
)");
    session.eval("func8()");

    session.eval(R"(
function int func9;
    casex (foo)
        1: return 1;
    endcase
    return 2;
endfunction
)");
    session.eval("func9()");

    session.eval(R"(
function int func10(int foo);
    case (foo) inside
        0: return -1;
        1: return 1;
    endcase
    return 2;
endfunction
)");
    CHECK(session.eval("func10(0)").integer() == -1);

    session.eval(R"(
function int func11(int foo);
    automatic int asdf[3] = '{ 1, 3, 5 };
    case (foo) inside
        asdf: return 9;
    endcase
    return 2;
endfunction
)");
    CHECK(session.eval("func11(4)").integer() == 2);
    CHECK(session.eval("func11(5)").integer() == 9);

    session.eval(R"(
function int func12(logic [3:0] foo);
    case (foo) inside
        4'b1x?1: return 1;
        4'b1?10: return 2;
    endcase
    return 3;
endfunction
)");
    CHECK(session.eval("func12(4'b1011)").integer() == 1);
    CHECK(session.eval("func12(4'bx110)").integer() == 3);

    session.eval(R"(
function int func13(logic [3:0] foo);
    case (foo) inside
        [5'd1:5'd2]: return 1;
        [5'd3:5'd20]: return 2;
    endcase
    return 3;
endfunction
)");
    CHECK(session.eval("func13(4'd2)").integer() == 1);
    CHECK(session.eval("func13(4'd10)").integer() == 2);
    CHECK(session.eval("func13(4'd0)").integer() == 3);
}

TEST_CASE("Eval sformatf") {
    ScriptSession session;
    session.eval("logic [125:0] foo = '0;");
    session.eval("logic signed [125:0] bar = '1;");
    session.eval("logic signed [125:0] baz = 1;");

    auto sformatf = [&](auto str, auto args) {
        return session.eval("$sformatf(\""s + str + "\", " + args + ")").str();
    };

    CHECK(session.eval("$sformatf(\"\")"s).str() == "");
    CHECK(sformatf("%d", "foo") == "                                     0");
    CHECK(sformatf("%0d", "foo") == "0");
    CHECK(sformatf("%2D", "foo") == " 0");
    CHECK(sformatf("%-2D", "foo") == "0 ");
    CHECK(sformatf("%d", "bar") == "                                     -1");
    CHECK(sformatf("%D", "baz") == "                                      1");

    CHECK(sformatf("%h", "foo") == "00000000000000000000000000000000");
    CHECK(sformatf("%H", "bar") == "3fffffffffffffffffffffffffffffff");
    CHECK(sformatf("%x", "baz") == "00000000000000000000000000000001");

    CHECK(sformatf("%o", "foo") == "000000000000000000000000000000000000000000");
    CHECK(sformatf("%O", "bar") == "777777777777777777777777777777777777777777");
    CHECK(sformatf("%o", "baz") == "000000000000000000000000000000000000000001");

    CHECK(sformatf("%8b", "foo") == "00000000");
    CHECK(sformatf("%8B", "bar[7:0]") == "11111111");
    CHECK(sformatf("%8b", "baz") == "00000001");

    CHECK(sformatf("%D", "1'bx") == "x");
    CHECK(sformatf("%X", "14'bx01010") == "xxXa");
    CHECK(sformatf("%h %o", "12'b001xxx101x01, 12'b001xxx101x01") == "XXX 1x5X");

    session.eval("real r = 3.21;");
    CHECK(sformatf("%F", "r") == "3.210000");
    CHECK(sformatf("%e", "r") == "3.210000e+00");
    CHECK(sformatf("%-10.1g", "r") == "3         ");
    CHECK(sformatf("%-010.f", "r") == "3         ");
    CHECK(sformatf("%010.f", "r") == "0000000003");
    CHECK(sformatf("%.f", "r") == "3");
    CHECK(sformatf("%.9f", "r") == "3.210000000");

    session.eval("string str = \"blah\";");
    CHECK(sformatf("%s", "\"abc\"") == "abc");
    CHECK(sformatf("%3s%%", "\"a\"") == "  a%");
    CHECK(sformatf("%3s", "\"abc\"") == "abc");
    CHECK(sformatf("%3s", "\"abcdef\"") == "abcdef");
    CHECK(sformatf("%3s", "str") == "blah");
    CHECK(sformatf("%0h", "str") == "626c6168");

    CHECK(sformatf("%c", "48") == "0");
    CHECK(sformatf("%c", "18'hx031") == "1");
    CHECK(sformatf("%c", "999") == "\xe7");

    CHECK(session.eval("$sformatf(\"%m\")"s).str() == "$unit");
    CHECK(session.eval("$sformatf(\"%l\")"s).str() == "work.$unit");

    session.eval(R"(
function string func;
    begin : baz
        return $sformatf("%m");
    end
endfunction
)");
    CHECK(session.eval("func()").str() == "func.baz");

    CHECK(sformatf("%u", "14'ha2c") == "\x2c\x0a\0\0"s);
    CHECK(sformatf("%z", "14'hzX2c") == "\x2c\x0f\0\0\0\x3f\0\0"s);

    CHECK(sformatf("%v", "1'b1") == "St1");
    CHECK(sformatf("%v", "1'b0") == "St0");
    CHECK(sformatf("%v", "1'bx") == "StX");
    CHECK(sformatf("%v", "1'bz") == "HiZ");
    CHECK(sformatf("%v", "3'b1z0") == "St1 HiZ St0");

    CHECK(sformatf("%t", "12345") == "               12345");

    session.eval(R"(
typedef enum {ON, OFF} switch_e;
typedef struct {switch_e sw; string s;} pair_t;
localparam pair_t va[int] = '{10:'{OFF, "switch10"}, 20:'{ON, "switch20"}};
localparam union packed { struct packed { logic [3:0] a; } a; logic [3:0] b; } up = 15;

localparam int da[] = '{3, 0, 0, 1};
localparam int fa[8] = '{2:4, default:1};
localparam int qa[$] = '{1, 2, 3};
localparam int aa[*] = '{3:1, 4:2, 5:3};

localparam switch_e eu = switch_e'(3);

typedef union tagged { void A; int B; } TaggedUnion;

localparam TaggedUnion tu1 = tagged A;
localparam TaggedUnion tu2 = tagged B 3;
localparam TaggedUnion tu3 = funcTU();

function automatic TaggedUnion funcTU();
    TaggedUnion tu;
    return tu;
endfunction
)");

    CHECK(sformatf("%p", "va") == "'{10:'{sw:OFF, s:\"switch10\"}, 20:'{sw:ON, s:\"switch20\"}}");
    CHECK(sformatf("%p", "\"Hello World\"") == "\"Hello World\"");
    CHECK(sformatf("%0p", "va") == "'{10:'{OFF,\"switch10\"},20:'{ON,\"switch20\"}}");
    CHECK(sformatf("%p", "up") == "'{a:4'b1111}");
    CHECK(sformatf("%p", "da") == "'{3, 0, 0, 1}");
    CHECK(sformatf("%0p", "fa") == "'{1,1,4,1,1,1,1,1}");
    CHECK(sformatf("%0p", "qa") == "'{1,2,3}");
    CHECK(sformatf("%p", "aa") == "'{3:1, 4:2, 5:3}");
    CHECK(sformatf("%p", "eu") == "3");
    CHECK(sformatf("%p", "tu1") == "A");
    CHECK(sformatf("%p", "tu2") == "B:3");
    CHECK(sformatf("%p", "tu3") == "(unset)");
    NO_SESSION_ERRORS;
}

TEST_CASE("sformatf with trailing percent") {
    ScriptSession session;
    CHECK(session.eval("$sformatf(\"a%\")"s).str() == "a%");
}

TEST_CASE("sformatf with real conversion") {
    ScriptSession session;
    CHECK(session.eval("$sformatf(\"%0d\", 3.14)"s).str() == "3");
}

TEST_CASE("Concat assignments") {
    ScriptSession session;
    session.eval("logic [2:0] foo;");
    session.eval("logic bar;");

    session.eval("{bar, foo} = 3'b111 + 2'd3");

    CHECK(session.eval("bar").integer() == 1);
    CHECK(session.eval("foo").integer() == 2);

    NO_SESSION_ERRORS;
}

TEST_CASE("Eval repeat loop") {
    ScriptSession session;
    session.eval(R"(
function automatic int foo(integer a);
    int result = 0;
    repeat (a) begin
        if (a == 8) return 8;
        if (result == 4) break;
        result++;
    end

    return result;
endfunction
)");

    CHECK(session.eval("foo('x)").integer() == 0);
    CHECK(session.eval("foo(1)").integer() == 1);
    CHECK(session.eval("foo(4)").integer() == 4);
    CHECK(session.eval("foo(9)").integer() == 4);
    CHECK(session.eval("foo(8)").integer() == 8);
    NO_SESSION_ERRORS;
}

TEST_CASE("Eval while loop") {
    ScriptSession session;
    session.eval(R"(
function automatic int foo(integer a);
    int result = 0;
    while (result < a) begin
        if (a == 8) return 8;
        if (result == 4) break;
        result++;
    end

    return result;
endfunction
)");

    CHECK(session.eval("foo(0)").integer() == 0);
    CHECK(session.eval("foo(1)").integer() == 1);
    CHECK(session.eval("foo(5)").integer() == 4);
    CHECK(session.eval("foo(2)").integer() == 2);
    CHECK(session.eval("foo(8)").integer() == 8);
    NO_SESSION_ERRORS;
}

TEST_CASE("Eval do-while loop") {
    ScriptSession session;
    session.eval(R"(
function automatic int foo(integer a);
    int result = 0;
    do begin
        if (a == 8) return 8;
        if (result == 4) break;
        result++;
    end
    while (result < a);

    return result;
endfunction
)");

    CHECK(session.eval("foo(0)").integer() == 1);
    CHECK(session.eval("foo(1)").integer() == 1);
    CHECK(session.eval("foo(5)").integer() == 4);
    CHECK(session.eval("foo(2)").integer() == 2);
    CHECK(session.eval("foo(8)").integer() == 8);
    NO_SESSION_ERRORS;
}

TEST_CASE("Eval forever loop") {
    ScriptSession session;
    session.eval(R"(
function automatic int foo(integer a);
    int result = 0;
    forever begin
        if (a == 8) return 8;
        if (result == 4) break;
        result++;
    end

    return result;
endfunction
)");

    CHECK(session.eval("foo(0)").integer() == 4);
    CHECK(session.eval("foo(1)").integer() == 4);
    CHECK(session.eval("foo(5)").integer() == 4);
    CHECK(session.eval("foo(2)").integer() == 4);
    CHECK(session.eval("foo(8)").integer() == 8);
    NO_SESSION_ERRORS;
}

TEST_CASE("Eval foreach loop") {
    ScriptSession session;
    session.eval(R"(
function automatic int foo();
    bit [1:0][2:1] asdf [3:-1][2];
    int qq = 7;

    int result = 0;
    foreach (asdf[a,b,,d]) begin
        if (b == 1)
            continue;
        result += a;
        result += b * 10;
        result += d * 100;
    end

    foreach (asdf[]) begin
        result += 99;
    end

    foreach (qq[i]) begin
        result += qq[i];
    end

    return result;
endfunction
)");

    auto cv = session.eval("foo()");
    CHECK(cv.integer() == 1513);
    NO_SESSION_ERRORS;
}

TEST_CASE("Eval foreach loop dynamic") {
    ScriptSession session;
    session.eval(R"(
function automatic int foo();
    int result = 0;
    int asdf [3][];
    int baz [2][string][$];
    string str = "Hello";

    asdf[0] = '{1, 2, 3, 4};
    asdf[2] = '{10, 11};

    foreach (asdf[a, b]) begin
        result += asdf[a][b];
        if (a == 2 && b == 1)
            break;
    end

    baz[0] = '{"hello": '{6, 4}, "world": '{9, -1}};

    foreach (baz[a, b, c]) begin
        result += baz[a][b][c];
        if (b == "world")
            result++;
    end

    foreach (str[s]) begin
        if (str[s] == "l")
            result++;
    end

    return result;
endfunction
)");

    CHECK(session.eval("foo()").integer() == 53);
    NO_SESSION_ERRORS;
}

TEST_CASE("Eval disable statement") {
    ScriptSession session;
    session.eval(R"(
function int foo;
    automatic int result = 0;
    begin : bar
        for (int i = 0; i < 5; i++) begin : baz
            for (int j = 0; j < 4; j++) begin : boz
                if (j == 2)
                    disable boz;
                result++;
                if (j == 3)
                    disable baz;
            end
            if (i == 3)
                disable bar;
        end
    end
    return result;
  endfunction
)");

    CHECK(session.eval("foo()").integer() == 15);
    NO_SESSION_ERRORS;
}

TEST_CASE("Eval enum methods") {
    ScriptSession session;
    session.eval("typedef enum { SDF = 2, BAR[5] = 4, BAZ = 99 } e_t;");
    session.eval("e_t asdf = BAR1;");

    CHECK(session.eval("asdf.next").integer() == 6);
    CHECK(session.eval("asdf.next(4)").integer() == 99);
    CHECK(session.eval("asdf.next(5)").integer() == 2);
    CHECK(session.eval("asdf.next(7)").integer() == 5);
    CHECK(session.eval("asdf.next(699)").integer() == 4);
    CHECK(session.eval("asdf.next(1'bx)").integer() == 5);

    CHECK(session.eval("asdf.name").str() == "BAR1");
    CHECK(session.eval("asdf.next(4).name").str() == "BAZ");
    CHECK(session.eval("asdf.next(4).name()").str() == "BAZ");

    CHECK(session.eval("asdf.prev").integer() == 4);
    CHECK(session.eval("asdf.prev(2)").integer() == 2);
    CHECK(session.eval("asdf.prev(3)").integer() == 99);
    CHECK(session.eval("asdf.prev(7)").integer() == 5);
    CHECK(session.eval("asdf.prev(699)").integer() == 6);
    CHECK(session.eval("asdf.prev(1'bx)").integer() == 5);

    session.eval("asdf = e_t'(1)");
    CHECK(session.eval("asdf.next").integer() == 0);
    CHECK(session.eval("asdf.prev(3)").integer() == 0);
    CHECK(session.eval("asdf.name()").str() == "");

    NO_SESSION_ERRORS;
}

TEST_CASE("Eval string methods") {
    ScriptSession session;
    session.eval("string asdf = \"BaR1\";");

    CHECK(session.eval("asdf.len").integer() == 4);
    CHECK(session.eval("asdf.toupper").str() == "BAR1");
    CHECK(session.eval("asdf.tolower").str() == "bar1");

    session.eval("asdf.putc(-1, 71);");
    CHECK(session.eval("asdf").str() == "BaR1");
    session.eval("asdf.putc(2, \"G\");");
    CHECK(session.eval("asdf").str() == "BaG1");

    CHECK(session.eval("asdf.getc(3)").integer() == '1');
    CHECK(session.eval("asdf.getc(4)").integer() == 0);
    CHECK(session.eval("asdf.getc(0)").integer() == 'B');

    CHECK(session.eval("asdf.compare(\"BaG2\")").integer() == -1);
    CHECK(session.eval("asdf.compare(\"BaG0\")").integer() == 1);
    CHECK(session.eval("asdf.compare(\"BaG1\")").integer() == 0);

    CHECK(session.eval("asdf.icompare(\"baG2\")").integer() == -1);
    CHECK(session.eval("asdf.icompare(\"bAg0\")").integer() == 1);
    CHECK(session.eval("asdf.icompare(\"bAG1\")").integer() == 0);

    CHECK(session.eval("asdf.substr(1, 4)").str() == "");
    CHECK(session.eval("asdf.substr(1, 3)").str() == "aG1");
    CHECK(session.eval("asdf.substr(3, 3)").str() == "1");

    CHECK(session.eval("asdf.atoi").integer() == 0);

    session.eval("asdf = \"1_23_4asdf\";");
    CHECK(session.eval("asdf.atoi").integer() == 1234);

    session.eval("asdf = \"1_23_4afdf\";");
    CHECK(session.eval("asdf.atohex").integer() == 0x1234afdf);

    session.eval("asdf = \"1_23_4078afdf\";");
    CHECK(session.eval("asdf.atooct").integer() == 0123407);

    session.eval("asdf = \"1_1_01afdf\";");
    CHECK(session.eval("asdf.atobin").integer() == 0b1101);

    session.eval("asdf = \"3.141__5_9e+9asdf\";");
    CHECK(session.eval("asdf.atoreal").real() == 3.14159e9);

    session.eval("asdf.itoa(1234);");
    CHECK(session.eval("asdf").str() == "1234");

    session.eval("asdf.hextoa(1234);");
    CHECK(session.eval("asdf").str() == "4d2");

    session.eval("asdf.octtoa(1234);");
    CHECK(session.eval("asdf").str() == "2322");

    session.eval("asdf.bintoa(1234);");
    CHECK(session.eval("asdf").str() == "10011010010");

    session.eval("asdf.realtoa(3.14159);");
    CHECK(session.eval("asdf").str() == "3.141590");

    NO_SESSION_ERRORS;
}

TEST_CASE("Eval inside expressions") {
    ScriptSession session;
    session.eval("int i = 4;");
    session.eval("int arr1[3] = '{ 1, 2, 3 };");
    session.eval("int arr2[3] = '{ 1, 2, 4 };");

    CHECK(session.eval("i inside { 1, 2, 3, 3'sb101, arr1 }").integer() == 0);
    CHECK(session.eval("i inside { 3'sb101, arr2 }").integer() == 1);
    CHECK_THAT((logic_t)session.eval("3'bx10 inside { 3'b101, arr2 }").integer(),
               exactlyEquals(logic_t::x));
    CHECK(session.eval("3'bx10 inside { 3'bxx0, arr2 }").integer() == 1);

    CHECK(session.eval("4 inside { 1, 2, [3:5] }").integer() == 1);
    CHECK(session.eval("4 inside { 1, 2, [-3:3] }").integer() == 0);

    session.eval("string s = \"asdf\";");
    CHECK(session.eval("s inside { \"foo\", [\"aaaa\" : \"bbbb\"] }").integer() == 1);
    CHECK(session.eval("s inside { \"foo\", [\"bbbb\" : \"cccc\"] }").integer() == 0);
    CHECK(session.eval("s inside { [\"bbbb\" : \"cccc\"], \"asdf\" }").integer() == 1);

    NO_SESSION_ERRORS;
}

TEST_CASE("Real conversion functions") {
    ScriptSession session;

    CHECK(session.eval("$rtoi(123.678)").integer() == 123);
    CHECK(session.eval("$rtoi(50000000000.0)").integer() == -1539607552);

    CHECK(session.eval("$itor(123)").real() == 123.0);
    CHECK(session.eval("$itor('x)").real() == 0.0);

    CHECK(session.eval("$realtobits(123.456)").integer() == 4638387860618067575ull);
    CHECK(session.eval("$bitstoreal(64'd4638387860618067575)").real() == 123.456);

    CHECK(session.eval("$shortrealtobits(123.456)").integer() == 1123477881);
    CHECK(session.eval("$bitstoshortreal(1123477881)").shortReal() == 123.456f);

    NO_SESSION_ERRORS;
}

TEST_CASE("Real math functions") {
    ScriptSession session;

    CHECK(session.eval("$ln(123.456)").real() == Approx(log(123.456)));
    CHECK(session.eval("$log10(123.456)").real() == Approx(log10(123.456)));
    CHECK(session.eval("$exp(123.456)").real() == Approx(exp(123.456)));
    CHECK(session.eval("$sqrt(123.456)").real() == Approx(sqrt(123.456)));
    CHECK(session.eval("$floor(123.456)").real() == Approx(floor(123.456)));
    CHECK(session.eval("$ceil(123.456)").real() == Approx(ceil(123.456)));
    CHECK(session.eval("$sin(123.456)").real() == Approx(sin(123.456)));
    CHECK(session.eval("$cos(123.456)").real() == Approx(cos(123.456)));
    CHECK(session.eval("$tan(123.456)").real() == Approx(tan(123.456)));
    CHECK(session.eval("$asin(0.456)").real() == Approx(asin(0.456)));
    CHECK(session.eval("$acos(0.456)").real() == Approx(acos(0.456)));
    CHECK(session.eval("$atan(0.456)").real() == Approx(atan(0.456)));
    CHECK(session.eval("$sinh(0.456)").real() == Approx(sinh(0.456)));
    CHECK(session.eval("$cosh(0.456)").real() == Approx(cosh(0.456)));
    CHECK(session.eval("$tanh(0.456)").real() == Approx(tanh(0.456)));
    CHECK(session.eval("$asinh(0.456)").real() == Approx(asinh(0.456)));
    CHECK(session.eval("$acosh(123.456)").real() == Approx(acosh(123.456)));
    CHECK(session.eval("$atanh(0.456)").real() == Approx(atanh(0.456)));

    CHECK(session.eval("$pow(2.1, 1.456)").real() == Approx(pow(2.1, 1.456)));
    CHECK(session.eval("$atan2(2.1, 1.456)").real() == Approx(atan2(2.1, 1.456)));
    CHECK(session.eval("$hypot(2.1, 1.456)").real() == Approx(hypot(2.1, 1.456)));

    NO_SESSION_ERRORS;
}

TEST_CASE("Bit vector functions") {
    ScriptSession session;

    session.eval("logic [13:0] asdf = 14'b101xz001zx1;");
    CHECK(session.eval("$countbits(asdf, '1)").integer() == 4);
    CHECK(session.eval("$countbits(asdf, '1, 0, 1)").integer() == 10);
    CHECK(session.eval("$countbits(asdf, 'x)").integer() == 2);
    CHECK(session.eval("$countbits(asdf, 'z, 'z, 'z, 'z)").integer() == 2);
    CHECK(session.eval("$countbits(asdf, 'z, 'x, '1, '0)").integer() == 14);
    CHECK(session.eval("$countones(asdf)").integer() == 4);

    session.eval("logic [13:0] bar = 14'b000100xzxz;");
    session.eval("logic [13:0] baz = 14'b000000xzxz;");
    CHECK(session.eval("$onehot(asdf)").integer() == 0);
    CHECK(session.eval("$onehot(bar)").integer() == 1);
    CHECK(session.eval("$onehot(baz)").integer() == 0);

    CHECK(session.eval("$onehot0(asdf)").integer() == 0);
    CHECK(session.eval("$onehot0(bar)").integer() == 1);
    CHECK(session.eval("$onehot0(baz)").integer() == 1);

    CHECK(session.eval("$isunknown(asdf)").integer() == 1);
    CHECK(session.eval("$isunknown(14'b101010101)").integer() == 0);
    CHECK(session.eval("$isunknown(14'b101z10101)").integer() == 1);

    session.eval("struct { int i; logic j[]; } foo = '{42, '{'x, 1, 0}};");
    CHECK(session.eval("$countbits(foo, '1, 'x)").integer() == 5);
    CHECK(session.eval("$countones(foo)").integer() == 4);
    CHECK(session.eval("$isunknown(foo)").integer() == 1);

    NO_SESSION_ERRORS;
}

TEST_CASE("Array query functions") {
    ScriptSession session;
    session.eval("logic [-1:15] up_vect = 5'b10111;");
    session.eval("logic [15:2] down_vect = 5'd25;");

    EVAL("$left(up_vect)", -1);
    EVAL("$right(up_vect)", 15);
    EVAL("$left(down_vect)", 15);
    EVAL("$right(down_vect)", 2);

    EVAL("$low(up_vect)", -1);
    EVAL("$high(up_vect)", 15);
    EVAL("$low(down_vect)", 2);
    EVAL("$high(down_vect)", 15);

    EVAL("$size(up_vect)", 17);
    EVAL("$size(down_vect)", 14);

    EVAL("$bits(up_vect)", 17);
    EVAL("$bits(down_vect)", 14);

    EVAL("$increment(up_vect)", -1);
    EVAL("$increment(down_vect)", 1);

    session.eval("integer i = -1;");
    session.eval("integer j = 10;");
    session.eval("integer k = 5;");
    session.eval("logic [3:1][2:4] arr [3][];");

    EVAL("$left(arr, i)", SVInt::createFillX(32, true));
    EVAL("$low(arr, k)", SVInt::createFillX(32, true));
    EVAL("$increment(arr, 3)", 1);

    for (auto& func : {"$left", "$right", "$low", "$high", "$increment", "$size"}) {
        EVAL(func + "(arr, j)"s, SVInt::createFillX(32, true));
    }

    session.eval("arr[1] = '{1, 2, 3};");
    EVAL("$left(arr[1])", 0);
    EVAL("$right(arr[1])", 2);
    EVAL("$low(arr[1])", 0);
    EVAL("$high(arr[1])", 2);
    EVAL("$increment(arr[1])", -1);
    EVAL("$size(arr[1])", 3);
    EVAL("$size(arr[0])", 0);
    EVAL("$right(arr[0])", -1);

    session.eval("string s = \"asdf\";");
    EVAL("$left(s)", 0);
    EVAL("$right(s)", 3);
    EVAL("$low(s)", 0);
    EVAL("$high(s)", 3);
    EVAL("$increment(s)", -1);
    EVAL("$size(s)", 4);

    EVAL("$dimensions(s)", 1);
    EVAL("$unpacked_dimensions(s)", 0);
    EVAL("$dimensions(arr)", 4);
    EVAL("$unpacked_dimensions(arr)", 2);
    EVAL("$dimensions(logic)", 0);
    EVAL("$unpacked_dimensions(logic)", 0);

    SVInt highVal(67, 0, false);
    highVal.setAllOnes();

    session.eval("int aa[logic[66:0]] = '{999999:4, 123:9, 5:72};");
    EVAL("$left(aa)", 0);
    EVAL("$right(aa)", highVal);
    EVAL("$low(aa)", 5);
    EVAL("$high(aa)", 999999);
    EVAL("$size(aa)", 3);
    EVAL("$increment(aa)", -1);
    EVAL("$dimensions(aa)", 2);
    EVAL("$unpacked_dimensions(aa)", 1);

    SVInt allX = SVInt::createFillX(67, false);
    session.eval("var type(aa) bb;");
    session.eval("aa = bb;");
    EVAL("$size(aa)", 0);
    EVAL("$low(aa)", allX);
    EVAL("$high(aa)", allX);

#undef EVAL

    NO_SESSION_ERRORS;
}

TEST_CASE("Static variables aren't initialized in consteval") {
    ScriptSession session;

    session.eval(R"(
function int foo;
    static int j = 1;
    return ++j;
endfunction
)");
    session.eval("localparam int i = foo();");

    CHECK(session.eval("i").integer() == 1);

    auto diags = session.getDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstEvalStaticSkipped);
}

TEST_CASE("Complicated lvalue path") {
    ScriptSession session;
    session.eval(R"(
struct { logic [4:1][2:9] foo[3][]; } asdf [4][][string][int];
)");
    session.eval("asdf[1] = new[3];");
    session.eval("asdf[1][2][\"hello\"][-9876].foo[0] = new[9];");
    session.eval("asdf[1][2][\"hello\"][-9876].foo[0][7][4] = 0;");
    session.eval("asdf[1][2][\"hello\"][-9876].foo[0][7][4][2:4] += 3'd7;");

    auto cv = session.eval("asdf[1][2][\"hello\"][-9876].foo[0][7][4]");
    CHECK(cv.integer() == 224);

    NO_SESSION_ERRORS;
}

TEST_CASE("Unpacked array concat") {
    ScriptSession session;
    session.eval("string S, hello = \"hello\";");
    session.eval("string SA[2];");
    session.eval("byte B;");
    session.eval("byte BA[2];");

    session.eval("S = {hello, \" world\"};");
    session.eval("SA = {hello, \" world\"};");
    session.eval("B = {4'h6, 4'hf};");
    session.eval("BA = {4'h6, 4'hf};");

    CHECK(session.eval("S").str() == "hello world");
    auto cv = session.eval("SA");
    CHECK(cv.elements()[0].str() == "hello");
    CHECK(cv.elements()[1].str() == " world");

    CHECK(session.eval("B").integer() == 0x6f);
    cv = session.eval("BA");
    CHECK(cv.elements()[0].integer() == 0x6);
    CHECK(cv.elements()[1].integer() == 0xf);

    session.eval("real RA[] = {1.2, 3.6};");
    cv = session.eval("BA = {RA}");
    CHECK(cv.elements()[0].integer() == 1);
    CHECK(cv.elements()[1].integer() == 4);

    session.eval("string SAD[] = {\"asdf\", \"foo\", \"bar\"};");
    CHECK(session.eval("SA = {SAD}").bad());

    auto diags = session.getDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::ConstantConversion);
    CHECK(diags[1].code == diag::ConstantConversion);
    CHECK(diags[2].code == diag::UnpackedConcatSize);
}

TEST_CASE("$bits unpacked types") {
    ScriptSession session;
    session.eval(R"(
localparam string str = "hello";
logic [0:2] fixed [17:13];
struct { time a; enum bit [0:1] {red, yellow, blue} b; } record;
localparam bit dynamic[] = '{1, 0};
localparam shortint queue[$] = '{8, 1, 3};
localparam byte asso[string] = '{ "Jon": 20, "Paul":22, "Al":23, default:-1 };
union { int i[4]; bit [18:0] j; } u;
)");

    CHECK(session.eval("$bits(str)").integer() == 40);
    CHECK(session.eval("$bits(fixed)").integer() == 15);
    CHECK(session.eval("$bits(record)").integer() == 66);
    CHECK(session.eval("$bits(dynamic)").integer() == 2);
    CHECK(session.eval("$bits(queue)").integer() == 48);
    CHECK(session.eval("$bits(asso)").integer() == 24);
    CHECK(session.eval("$bits(\"abcefghijk\")").integer() == 80);
    CHECK(session.eval("$bits(0)").integer() == 32);
    CHECK(session.eval("$bits(u)").integer() == 128);

    NO_SESSION_ERRORS;
}

TEST_CASE("bit-stream cast evaluation") {
    ScriptSession session;
    session.eval(R"(
localparam struct {bit a[$]; shortint b; string c; logic[3:0]d;} a = '{{1,0,1,0}, 67, "$", 4'b1x1z};
localparam integer tab [string] = '{"Peter":20, "Paul":22, "Mary":23, default:-1 };
typedef int b[5:7];
localparam string str = "hello!!";
typedef struct { shortint a[]; byte b[-2:-4]; } c;
typedef struct { bit[0:4] a; bit[8:3] b; bit[38:0] c; bit[10:15] d; } d;
localparam bit[7:1] e [0:7] = {29, 40, 0, 0, 0, 3, 99, 125};
typedef struct { logic[-2:5] a[][]; string b; bit c[$]; } f;
)");

    CHECK(session.eval("int'(a)").integer() == -1610337718);

    auto cv0 = session.eval("b'(tab)");
    CHECK(cv0.elements()[0].integer() == 23);
    CHECK(cv0.elements()[1].integer() == 22);
    CHECK(cv0.elements()[2].integer() == 20);
    CHECK(cv0.elements().size() == 3);

    auto cv1 = session.eval("c'(str)");
    CHECK(cv1.elements()[0].elements()[0].integer() == 26725);
    CHECK(cv1.elements()[0].elements()[1].integer() == 27756);
    CHECK(cv1.elements()[0].elements().size() == 2);
    CHECK(cv1.elements()[1].elements()[0].integer() == 'o');
    CHECK(cv1.elements()[1].elements()[1].integer() == '!');
    CHECK(cv1.elements()[1].elements()[2].integer() == '!');
    CHECK(cv1.elements()[1].elements().size() == 3);
    CHECK(cv1.elements().size() == 2);
    CHECK(session.eval("string'(c'(str))").str() == "hello!!");
    CHECK(session.eval("string'(d'(str))").str() == "hello!!");

    auto cv2 = session.eval("d'(e)");
    CHECK(cv2.elements()[0].integer() == 7);
    CHECK(cv2.elements()[1].integer() == 21);
    CHECK(cv2.elements()[2].integer() == 967);
    CHECK(cv2.elements()[3].integer() == 61);
    CHECK(cv2.elements().size() == 4);

    auto cv3 = session.eval("f'(e)");
    CHECK(cv3.elements()[0].elements().size() == 1);
    CHECK(cv3.elements()[0].elements()[0].elements().size() == 7);
    CHECK(cv3.elements()[0].elements()[0].elements()[0].integer() == 58);
    CHECK(cv3.elements()[0].elements()[0].elements()[1].integer() == 160);
    CHECK(cv3.elements()[0].elements()[0].elements()[2].integer() == 0);
    CHECK(cv3.elements()[0].elements()[0].elements()[3].integer() == 0);
    CHECK(cv3.elements()[0].elements()[0].elements()[4].integer() == 0);
    CHECK(cv3.elements()[0].elements()[0].elements()[5].integer() == 241);
    CHECK(cv3.elements()[0].elements()[0].elements()[6].integer() == 253);
    CHECK(cv3.elements()[1].str().empty());
    CHECK(cv3.elements()[2].queue()->empty());
    CHECK(cv3.elements().size() == 3);

    NO_SESSION_ERRORS;
}

TEST_CASE("Mixed unknowns or signedness") {
    ScriptSession session;

    // bitwise operator with exactly one operand unknown
    CHECK_THAT(session.eval("3'b000 ^ 3'b0x1").integer(), exactlyEquals("3'b0x1"_si));
    CHECK_THAT(session.eval("3'b0x1 ^ 3'b000").integer(), exactlyEquals("3'b0x1"_si));
    CHECK_THAT(session.eval("3'b000 | 3'b0x1").integer(), exactlyEquals("3'b0x1"_si));
    CHECK_THAT(session.eval("3'b0x1 | 3'b000").integer(), exactlyEquals("3'b0x1"_si));
    CHECK_THAT(session.eval("3'b111 & 3'b0x1").integer(), exactlyEquals("3'b0x1"_si));
    CHECK_THAT(session.eval("3'b0x1 & 3'b111").integer(), exactlyEquals("3'b0x1"_si));
    CHECK_THAT(session.eval("3'b000 ~^ 3'b0x1").integer(), exactlyEquals("3'b1x0"_si));
    CHECK_THAT(session.eval("3'b0x1 ^~ 3'b000").integer(), exactlyEquals("3'b1x0"_si));
    CHECK_THAT(session.eval("599'b000 ^ 3'b0x1").integer(), exactlyEquals("599'b0x1"_si));
    CHECK_THAT(session.eval("3'b0x1 ^ 600'b0").integer(), exactlyEquals("600'b0x1"_si));
    CHECK_THAT(session.eval("3'b0x1 | 601'b0").integer(), exactlyEquals("601'b0x1"_si));
    CHECK_THAT(session.eval("3'b0x1 & {602{1'b1}}").integer(), exactlyEquals("602'b0x1"_si));
    CHECK_THAT(session.eval("3'b0x1 ^~ {{600{1'b1}}, 3'b0}").integer(),
               exactlyEquals("603'b1x0"_si));

    // logical and reduction operators on mixed unknowns
    CHECK(session.eval("! 3'b0x1").integer() == 0);
    CHECK(session.eval("| 3'b0x1").integer() == 1);
    CHECK(session.eval("& 3'b0x1").integer() == 0);
    CHECK_THAT(session.eval("& 3'bx1").integer(), exactlyEquals(SVInt(logic_t::x)));
    CHECK(session.eval("3'b0x1 || 1'b0").integer() == 1);
    CHECK(session.eval("3'b0x1 && 1'b1").integer() == 1);
    CHECK(session.eval("&65'bx10").integer() == 0);
    CHECK_THAT(session.eval("&65'bx1").integer(), exactlyEquals(SVInt(logic_t::x)));

    // equality operators with unknowns
    CHECK(session.eval("3'b0x1 == 0").integer() == 0);
    CHECK(session.eval("2'b1x ? 16'h1234 : 16'h7890").integer() == 4660);
    CHECK_THAT(session.eval("3'sb1x0 == 4'sb11x0").integer(), exactlyEquals(SVInt(logic_t::x)));
    CHECK(session.eval("{1'b1, 99'b0x0} == 0").integer() == 0);

    // mixed signed
    CHECK(session.eval("1'b0 ? 7'd100 : 3'sb101").integer() == 5);
    CHECK(session.eval("3'sd2**2'b10 > -2").integer() == 1);
    CHECK(session.eval("-1**2'b11").integer() == -1);
    CHECK(session.eval("500'habcdef**-2").integer() == 0);
    CHECK(session.eval("-500'sd1**7'd37").integer() == -1);
    CHECK(session.eval("-500'sd1**-3").integer() == -1);
    CHECK(session.eval("4'd3**500'sd3").integer() == 11);
    CHECK(session.eval("10**3'b100").integer() == 10000);
    CHECK(session.eval("3'b111**2'sb10").integer() == 0);
    CHECK(session.eval("3'b111**2'sb10").integer() == 0);
    CHECK(session.eval("(-5'sd10 / 5'sd3) + 2'b01").integer() == 8);
    CHECK(session.eval("(5'sd3 - 5'sd10) + 2'b01").integer() == 26);

    // shift operators negative right operand or with unknonws
    CHECK_THAT(session.eval("30'b10xz0110111<<-3'sb1").integer(),
               exactlyEquals("30'b00000000000010xz01101110000000"_si));
    CHECK_THAT(session.eval("5'sbz001x>>>2").integer(), exactlyEquals("5'bzzz00"_si));
    CHECK_THAT(session.eval("129'sb0xzxz>>>1").integer(), exactlyEquals("129'sb0xzx"_si));
    CHECK_THAT(session.eval("65'sbx >>> 66").integer(), exactlyEquals("65'sbx"_si));
    CHECK_THAT(session.eval("35'sbz >>> 66").integer(), exactlyEquals("35'sbz"_si));
    CHECK_THAT(session.eval("200'sbxz >>> 130").integer(), exactlyEquals("200'sbx"_si));

    // system functions with unknown arguments
    CHECK(session.eval("$itor(3'bz1x)").real() == 2.0);
    CHECK(session.eval("$clog2(3'bz1x)").integer() == 1);
    CHECK(session.eval("$clog2(-3'sb1)").integer() == 3);
    CHECK(session.eval("$itor(37'sh198765432d)").real() == -27793210579.0);
    CHECK(session.eval("$itor(66'h1 << 65)").real() == std::pow(2, 65));

    NO_SESSION_ERRORS;
}

TEST_CASE("Streaming operator const evaluation") {
    ScriptSession session;
    session.eval(R"(
localparam int j = { "A", "B", "C", "D" };
localparam int s0 = { >> {j}};
localparam int s1 = { << byte {j}};
localparam int s2 = { << 16 {j}};
localparam shortint s3 = { << { 8'b0011_0101 }};
localparam shortint s4 = { << 4 { 6'b11_0101 }};
localparam shortint unsigned s5 = { >> 4 { 6'b11_0101 }};
localparam shortint unsigned s6 = { << 2 { { << { 4'b1101 }} }};

localparam string str = "ABCD";
localparam string str0 = { >> {str}};
localparam string str1 = { << byte {str}};
localparam string str2 = { << 16 {str}};
localparam string j0 = { >> {j}};
localparam string j1 = { << byte {j}};
localparam string j2 = { << 16 {j}};
localparam int i0 = { >> {str}};
localparam int i1 = { << byte {str}};
localparam int i2 = { << 16 {str}};

localparam bit [7:0] array0[4] = '{ 8'h8C, 8'h00, 8'hA4, 8'hFF };
localparam int value0 = {<<16{array0}};
localparam bit [7:0] array1[2] = '{ 8'h8C, 8'hA4 };
localparam shortint value1 = {<<{array1}};
localparam bit [1:0] array2[] = '{ 2'b10, 2'b01, 2'b11, 2'b00 };
typedef struct {
    bit [3:0] addr;
    bit [3:0] data;
} packet_t;
localparam packet_t value2 = {<<4{ {<<2{array2}} }};

typedef union {
    byte b;
    logic[63:0] r;
} u_t;

function u_t f;
    f.b = byte'(8'b10011100);
endfunction

function u_t g;
    g.r = 123456789;
endfunction

localparam u_t value3 = f();
localparam logic[7:0] value4 = {<<4{ {<<2{value3}} }};

localparam u_t value5 = g();
localparam logic[7:0] value6 = {<<4{ {<<2{value5}} }};
)");

    CHECK(session.eval("s0").integer() == session.eval("{\"A\", \"B\", \"C\", \"D\"}").integer());
    CHECK(session.eval("s1").integer() == session.eval("{\"D\", \"C\", \"B\", \"A\"}").integer());
    CHECK(session.eval("s2").integer() == session.eval("{\"C\", \"D\", \"A\", \"B\"}").integer());
    CHECK(session.eval("s3").integer() == session.eval("$signed({8'b1010_1100, 8'b0})").integer());
    CHECK(session.eval("s4").integer() == session.eval("{6'b0101_11, 10'b0}").integer());
    CHECK(session.eval("s5").integer() == session.eval("{6'b1101_01, 10'b0}").integer());
    CHECK(session.eval("s6").integer() == session.eval("{4'b1110, 12'b0}").integer());

    CHECK(session.eval("str0").str() == "ABCD");
    CHECK(session.eval("str1").str() == "DCBA");
    CHECK(session.eval("str2").str() == "CDAB");
    CHECK(session.eval("j0").str() == "ABCD");
    CHECK(session.eval("j1").str() == "DCBA");
    CHECK(session.eval("j2").str() == "CDAB");
    CHECK(session.eval("i0").integer() == session.eval("{\"A\", \"B\", \"C\", \"D\"}").integer());
    CHECK(session.eval("i1").integer() == session.eval("{\"D\", \"C\", \"B\", \"A\"}").integer());
    CHECK(session.eval("i2").integer() == session.eval("{\"C\", \"D\", \"A\", \"B\"}").integer());

    CHECK(session.eval("value0").integer() == "32'shA4FF_8C00"_si);
    CHECK(session.eval("value1").integer() == "16'h2531"_si);
    auto value2 = session.eval("value2");
    CHECK(value2.elements()[0].integer() == "4'b0110"_si);
    CHECK(value2.elements()[1].integer() == "4'b0011"_si);

    CHECK(session.eval("value4").integer() == "8'b01100011"_si);

    auto diags = session.getDiagnostics();
    REQUIRE(diags.size() == 2);
    CHECK(diags[0].code == diag::IgnoredSlice);
    CHECK(diags[1].code == diag::BadStreamSize);
}

TEST_CASE("streaming operator target evaluation") {
    ScriptSession session;
    session.eval(R"(
typedef bit ft[];
function bit [0:95] foo(ft bar);
    int a, b, c;
    {>>{a,{<<{b}},c}} = bar;
    return {a,b,c};
endfunction

typedef byte ft1[3];
function ft1 foo1(bit[1:26] bar);
    ft1 a;
    {<<16{{<<4{a[0]}},a[1],{<<3{a[2]}}}} = bar;
    return a;
endfunction

typedef struct { byte a[]; bit b;} ft2;
    function ft2 foo2(ft bar);
    ft2 a;
    {<<6{a}} = bar;
    return a;
endfunction

function ft2 foo3(ft bar);
    ft2 a;
    {<<11{a}} = {<<7{bar}};
    return a;
endfunction
)");

    CHECK(session.eval("foo(ft'(96'b1+(96'b1<<65)))").integer() ==
          session.eval("{32'd2, 32'd0, 32'd1}").integer());
    CHECK(session.eval("foo(ft'(100'b11111+(96'b1<<65)))").integer() ==
          session.eval("{32'd0, 32'd4, 32'd1}").integer());

    auto cv1 = session.eval("foo1({24'h123456, 2'b11})");
    CHECK(cv1.elements().size() == 3);
    CHECK(cv1.elements()[0].integer() == "8'sh65"_si);
    CHECK(cv1.elements()[1].integer() == "8'sh12"_si);
    CHECK(cv1.elements()[2].integer() == "8'sh29"_si);

    auto cv2 = session.eval("foo2(ft'({<<5{12'habc}}))");
    CHECK(cv2.elements().size() == 2);
    CHECK(cv2.elements()[0].elements().size() == 1);
    CHECK(cv2.elements()[0].elements()[0].integer() == "8'sh5c"_si);
    CHECK(cv2.elements()[1].integer() == 1);

    auto cv3 = session.eval("foo3({1'b1})");
    CHECK(cv3.elements().size() == 2);
    CHECK(cv3.elements()[0].elements().empty());
    CHECK(cv3.elements()[1].integer() == 1);

    NO_SESSION_ERRORS;
}

TEST_CASE("Recursive function call") {
    ScriptSession session;
    session.eval(R"(
function automatic integer factorial (input signed [31:0] operand);
    if (operand >= 2)
        factorial = factorial (operand - 1) * operand;
    else
        factorial = 1;
endfunction: factorial
)");

    CHECK(session.eval("factorial(6)").integer() == 720);

    NO_SESSION_ERRORS;
}

TEST_CASE("Stream with const evaluation") {
    ScriptSession session;
    session.eval(R"(
    localparam byte a[] = {"A", "B", "C", "D"};
    localparam int b = {>>{a with [3]}};
    localparam int c = {>>{a with [1+:2]}};
    localparam int d = {<<8{a with [2-:2]}};
    localparam int e = {<<16{a with [2:3]}};
    localparam byte q[$] = {3};
    localparam byte d1[] = {<<8{q with [2-:3]}};
    )");

    CHECK(session.eval("b").integer() == session.eval("{\"D\", 24'd0}").integer());
    CHECK(session.eval("c").integer() == session.eval("{\"B\", \"C\", 16'd0}").integer());
    CHECK(session.eval("d").integer() == session.eval("{\"C\", \"B\", 16'd0}").integer());
    CHECK(session.eval("e").integer() == session.eval("{\"C\", \"D\", 16'd0}").integer());
    CHECK(session.eval("byte'({>>{q with [2]}})").integer() == 0);
    auto cvD = session.eval("d1");
    CHECK(cvD.elements().size() == 3);
    CHECK(cvD.elements()[0].integer() == 0);
    CHECK(cvD.elements()[1].integer() == 0);
    CHECK(cvD.elements()[2].integer() == 3);

    session.eval(R"(
typedef byte ft1[6];
typedef byte ft2[];
function ft1 foo1(bit[1:26] bar, ft2 bar1);
    ft1 a;
    {<<16{{<<4{a with [0]}}, {>>{a with [1:1]}}, {<<3{a with [2+:1]}}}} = bar;
    {<<8{a with [5-:3]}} = {<<16{bar1 with [1+:3]}};
    return a;
endfunction
function ft2 foo2(bit[1:26] bar, ft2 bar1);
    ft2 a;
    {<<16{{<<4{a with [0]}}, {>>{a with [1:1]}}, {<<3{a with [2+:1]}}}} = bar;
    {<<8{a with [5-:3]}} = {<<16{bar1 with [1+:3]}};
    return a;
endfunction
typedef byte ft3[$];
function ft3 foo3(bit[1:24] bar);
    ft3 a;
    {<<8{a with [2:4]}} = {>>{bar}};
    return a;
endfunction
function ft3 foo4(bit[1:24] bar);
    ft3 a;
    {>>{a with [2]}} = bar;
    return a;
endfunction
)");

    auto cv1 = session.eval("foo1({24'h123456, 2'b11}, \"ABCDEF\")");
    CHECK(cv1.elements().size() == 6);
    CHECK(cv1.elements()[0].integer() == "8'sh65"_si);
    CHECK(cv1.elements()[1].integer() == "8'sh12"_si);
    CHECK(cv1.elements()[2].integer() == "8'sh29"_si);
    CHECK(cv1.elements()[3].integer() == 'B');
    CHECK(cv1.elements()[4].integer() == 'D');
    CHECK(cv1.elements()[5].integer() == 'C');

    auto cv2 = session.eval("foo2({24'h123456, 2'b11}, \"ABCDEF\")");
    CHECK(cv2.elements().size() == 6);
    CHECK(cv2.elements()[0].integer() == "8'sh65"_si);
    CHECK(cv2.elements()[1].integer() == "8'sh12"_si);
    CHECK(cv2.elements()[2].integer() == "8'sh29"_si);
    CHECK(cv2.elements()[3].integer() == 'B');
    CHECK(cv2.elements()[4].integer() == 'D');
    CHECK(cv2.elements()[5].integer() == 'C');

    auto cv3 = session.eval("foo3(24'h123456)");
    auto queue3 = *cv3.queue();
    CHECK(queue3.size() == 5);
    CHECK(queue3[0].integer() == 0);
    CHECK(queue3[1].integer() == 0);
    CHECK(queue3[2].integer() == "8'sh56"_si);
    CHECK(queue3[3].integer() == "8'sh34"_si);
    CHECK(queue3[4].integer() == "8'sh12"_si);

    auto cv4 = session.eval("foo4(24'h123456)");
    auto queue4 = *cv4.queue();
    CHECK(queue4.size() == 3);
    CHECK(queue4[0].integer() == 0);
    CHECK(queue4[1].integer() == 0);
    CHECK(queue4[2].integer() == "8'sh12"_si);

    NO_SESSION_ERRORS;
}

TEST_CASE("Array reduction methods") {
    ScriptSession session;
    session.eval("byte b[] = { 1, 2, 3, 4 };");
    session.eval("logic [7:0] m [2][2] = '{ '{5, 10}, '{15, 20} };");
    session.eval("logic bit_arr [16] = '{0:1, 1:1, 2:1, default:0};");

    CHECK(session.eval("b.sum").integer() == 10);
    CHECK(session.eval("b.product").integer() == 24);
    CHECK(session.eval("b.xor with (item + 4)").integer() == 12);
    CHECK(session.eval("m.sum(a) with (a.sum with (a[0] + item));").integer() == 90);
    CHECK(session.eval("bit_arr.sum with ( int'(item) );").integer() == 3);

    NO_SESSION_ERRORS;
}

TEST_CASE("Array ordering methods") {
    ScriptSession session;
    session.eval("int a[] = {1, 4, 2, 9, 8, 8};");
    session.eval("int b[$] = {1, 4, -2, -9, -8, 8};");

    session.eval("a.sort");
    CHECK(session.eval("a").toString() == "[1,2,4,8,8,9]");
    session.eval("b.rsort with (item * -1)");
    CHECK(session.eval("b").toString() == "[-9,-8,-2,1,4,8]");

    session.eval("a.sort with (item == 2 ? 100 : item)");
    CHECK(session.eval("a").toString() == "[1,4,8,8,9,2]");
    session.eval("b.rsort");
    CHECK(session.eval("b").toString() == "[8,4,1,-2,-8,-9]");

    session.eval("int c[] = {1, 9, 4, 3};");
    session.eval("string d[$] = {\"asdf\", \"baz\", \"bar\"};");
    session.eval("c.reverse");
    session.eval("d.reverse");

    CHECK(session.eval("c").toString() == "[3,4,9,1]");
    CHECK(session.eval("d").toString() == "[\"bar\",\"baz\",\"asdf\"]");

    NO_SESSION_ERRORS;
}

TEST_CASE("Array locator methods") {
    ScriptSession session;
    session.eval("int a[] = {1, 4, 2, 9, 8, 8};");
    session.eval("int b[$] = {4, 1, -2, -9, -8, 8};");
    session.eval("int c[string] = '{\"hello\":1, \"good\":4, \"bye\":-2};");
    session.eval("int d[];");

    CHECK(session.eval("a.find with (item > 7)").toString() == "[9,8,8]");
    CHECK(session.eval("b.find_index with (item < 0)").toString() == "[2,3,4]");
    CHECK(session.eval("c.find_first with (item == 4)").toString() == "[4]");
    CHECK(session.eval("c.find_first_index with (item == 4)").toString() == "[\"good\"]");
    CHECK(session.eval("c.find_last with (item < 100)").toString() == "[1]");
    CHECK(session.eval("b.find_last_index with (item > 10)").toString() == "[]");
    CHECK(session.eval("a.find_last_index with (item == 8)").toString() == "[5]");

    CHECK(session.eval("b.min").toString() == "[-9]");
    CHECK(session.eval("b.min with (item * -1)").toString() == "[8]");
    CHECK(session.eval("c.max").toString() == "[4]");
    CHECK(session.eval("a.max with (item == 2 ? 99 : item)").toString() == "[2]");
    CHECK(session.eval("d.max").toString() == "[]");

    session.eval("int e[] = {1, 1, 4, 9, -3, 1, 2};");
    CHECK(session.eval("e.unique").toString() == "[1,4,9,-3,2]");
    CHECK(session.eval("e.unique_index").toString() == "[0,2,3,4,6]");
    CHECK(session.eval("e.unique with (item == 4 ? 1 : item)").toString() == "[1,9,-3,2]");
    CHECK(session.eval("e.unique_index with (item == 4 ? 1 : item)").toString() == "[0,3,4,6]");

    session.eval("int f[string] = '{\"a\":1, \"b\":5, \"c\":1, \"d\":1};");
    CHECK(session.eval("f.unique_index").toString() == "[\"a\",\"b\"]");
    CHECK(session.eval("f.unique_index with (item == 5 ? 1 : item)").toString() == "[\"a\"]");

    NO_SESSION_ERRORS;
}

TEST_CASE("Queue unbounded expressions") {
    ScriptSession session;
    session.eval("int q[$] = {1, 2, 4};");

    CHECK(session.eval("q[$]").integer() == 4);

    session.eval("q[$-1*2+1] = 9");
    CHECK(session.eval("q[1]").integer() == 9);

    CHECK(session.eval("q[1:$]").toString() == "[9,4]");

    session.eval("q[$-2:$-1] = {3, 6}");
    CHECK(session.eval("q").toString() == "[3,6,4]");

    session.eval("q[$+1] = -1;");
    CHECK(session.eval("q").toString() == "[3,6,4,-1]");

    session.eval("parameter int p1 = $;");
    session.eval("parameter p2 = $;");

    CHECK(session.eval("$isunbounded($)").integer() == 1);
    CHECK(session.eval("$isunbounded(p1)").integer() == 1);
    CHECK(session.eval("$isunbounded(p2)").integer() == 1);
    CHECK(session.eval("$isunbounded(0)").integer() == 0);
    CHECK(session.eval("$isunbounded(3.14)").integer() == 0);

    NO_SESSION_ERRORS;
}

TEST_CASE("Queue max bound limitation") {
    ScriptSession session;
    session.eval("int q[$:3] = {1, 2, 4};");

    session.eval("q.push_back(6)");
    session.eval("q.push_back(8)");
    CHECK(session.eval("q").toString() == "[1,2,4,6]");

    session.eval("q[$+1] = -1;");
    CHECK(session.eval("q").toString() == "[1,2,4,6]");

    session.eval("q = {9, 8, 7, 6, 5}");
    CHECK(session.eval("q").toString() == "[9,8,7,6]");

    session.eval("q.insert(2, -1)");
    CHECK(session.eval("q").toString() == "[9,8,-1,7]");

    NO_SESSION_ERRORS;
}

TEST_CASE("Assignment type propagation regression") {
    ScriptSession session;
    session.eval("logic [7:0] foo;");
    session.eval("logic signed [5:0] a = -1;");
    session.eval("logic signed [4:0] b = -2;");

    CHECK(session.eval("foo = a + b").integer() == 253);

    NO_SESSION_ERRORS;
}

TEST_CASE("Tagged union eval") {
    ScriptSession session;

    session.eval("union tagged { int a; real b; } u;");
    CHECK(session.eval("u").toString() == "(unset)");

    session.eval("u = tagged b 3.14;");
    CHECK(session.eval("u").toString() == "(1) 3.14");
    session.eval("u.a");
    session.eval("u.a = 1;");

    session.eval("union tagged packed { byte a; byte unsigned b; } v;");
    CHECK(session.eval("v").toString() == "9'd0");

    session.eval("v = tagged b 200;");
    CHECK(session.eval("v").toString() == "9'd456");
    CHECK(session.eval("v.b").integer() == 200);
    CHECK(session.eval("v.b = 5").integer() == 5);
    session.eval("v.a");
    session.eval("v.a = 1;");

    session.eval("v = tagged a -1;");
    CHECK(session.eval("v.a").integer().as<int8_t>() == -1);

    CHECK(session.eval("$bits(v)").integer() == 9);
    CHECK(session.eval("$bits(u)").integer() == 64);

    session.eval("union tagged { int a[]; real b; } w;");
    session.eval("w = tagged a '{1, 2, 3, 4}");
    CHECK(session.eval("$bits(w)").integer() == 128);

    auto diags = session.getDiagnostics();
    REQUIRE(diags.size() == 4);
    CHECK(diags[0].code == diag::ConstEvalTaggedUnion);
    CHECK(diags[1].code == diag::ConstEvalTaggedUnion);
    CHECK(diags[2].code == diag::ConstEvalTaggedUnion);
    CHECK(diags[3].code == diag::ConstEvalTaggedUnion);
}

TEST_CASE("Assignment pattern eval") {
    ScriptSession session;
    session.eval("typedef logic[7:0] bt;");
    session.eval("bt foo[4:3][1:2] = '{bt: 3};");

    CHECK(session.eval("foo").toString() == "[[8'd3,8'd3],[8'd3,8'd3]]");

    session.eval(R"(
struct {
    int a[1:0];
    time t;
    logic[6:1] l;
    union packed { int i; } u;
    struct { real r; } r[2];
} bar[1:2][4:3] = '{int:1, time:2, real:3.14, default:2};)");

    CHECK(session.eval("bar").toString() == "[[[[1,1],64'h2,6'b10,32'd2,[[3.14],[3.14]]],"
                                            "[[1,1],64'h2,6'b10,32'd2,[[3.14],[3.14]]]],"
                                            "[[[1,1],64'h2,6'b10,32'd2,[[3.14],[3.14]]],"
                                            "[[1,1],64'h2,6'b10,32'd2,[[3.14],[3.14]]]]]");

    session.eval("int q[$] = '{3{5}};");
    CHECK(session.eval("q").toString() == "[5,5,5]");

    session.eval("logic [11:0] r = '{12{4'd3}};");
    CHECK(session.eval("r").integer() == 4095);

    auto diags = session.getDiagnostics();
    REQUIRE(diags.size() == 1);
    CHECK(diags[0].code == diag::ConstantConversion);
}

TEST_CASE("foreach loop extended name eval") {
    ScriptSession session;
    session.eval("typedef int rt[2][2];");
    session.eval(R"(
function rt f;
    rt array;
    foreach (array[i]) begin
        foreach (array[i][j]) begin
            array[i][j] = (i + 1) * (j + 1);
        end
    end
    return array;
endfunction
)");

    auto cv = session.eval("f();");
    CHECK(cv.toString() == "[[1,2],[2,4]]");
}

TEST_CASE("for loop with no stop expression eval") {
    ScriptSession session;
    session.eval("typedef int rt[2][2];");
    session.eval(R"(
function automatic int f;
    int i = 0;
    for (;;) begin
        i++;
        if (i > 2)
            break;
    end
    return i;
endfunction
)");

    auto cv = session.eval("f();");
    CHECK(cv.toString() == "3");
    NO_SESSION_ERRORS;
}

TEST_CASE("Pattern matching eval") {
    ScriptSession session;
    session.eval(R"(
typedef union tagged {
    struct {
        bit [4:0] reg1, reg2, regd;
    } Add;
    union tagged {
        bit [9:0] JmpU;
        struct packed {
            bit [1:0] cc;
            bit [9:0] addr;
        } JmpC;
    } Jmp;
    void Baz;
} Instr;
)");

    session.eval(R"(
function automatic int f1;
    Instr e = tagged Jmp tagged JmpC '{2, 137};
    int rf[3] = '{0, 0, 1};

    if (e matches (tagged Jmp (tagged JmpC '{cc:.c,addr:.a}))
        &&& (rf[c] != 0))
        return int'(c + a);
    else
        return 1;
endfunction
)");

    session.eval(R"(
function automatic int f2;
    Instr e = tagged Jmp tagged JmpC '{2, 137};
    int rf[3] = '{0, 0, 1};
    int i = 1;
    struct { int a; real b; } asdf = '{1, 3.14};

    unique case (e) matches
        tagged Add: return 99;
    endcase

    case (e) matches
        tagged Jmp: i++;
    endcase

    case (e) matches
        tagged Add: return 100;
        default: i += 9;
    endcase

    unique case (e) matches
        tagged Jmp tagged JmpC '{.*, .*}: begin end
        tagged Jmp tagged JmpC '{.*, .*}: begin end
    endcase

    case (asdf) matches
        '{1.1, 3}: i++;
        '{1, 3.14}: i += 3;
    endcase

    casex (asdf) matches
        '{32'bx, 3.14}: i += 9;
    endcase

    casez (asdf) matches
        '{32'b?, 3.14}: i += 7;
    endcase

    case (e) matches
        tagged Add '{reg1:0}: return 2;
        tagged Jmp tagged JmpC '{2, 0}: return 3;
        tagged Jmp tagged JmpC '{.a, 137} &&& rf[0] > 0: return 4;
        tagged Jmp tagged JmpC '{.a, .b} &&& rf[2] == 1: return int'(a + b + unsigned'(i));
        default: return 0;
    endcase
endfunction
)");

    session.eval(R"(
function automatic logic[31:0] f3;
    Instr e = tagged Jmp tagged JmpC '{2, 137};
    int rf[3] = '{0, 0, 1};
    return e matches (tagged Jmp (tagged JmpC '{cc:.c,addr:.a})) &&& rf[c] != 0 ? c + a : 1;
endfunction
)");

    CHECK(session.eval("f1();").toString() == "139");
    CHECK(session.eval("f2();").toString() == "169");
    CHECK(session.eval("f3();").integer() == 139);

    auto diags = session.getDiagnostics();
    REQUIRE(diags.size() == 8);
    CHECK(diags[0].code == diag::ArithOpMismatch);
    CHECK(diags[1].code == diag::ConstEvalNoCaseItemsMatched);
    CHECK(diags[2].code == diag::ConstEvalCaseItemsNotUnique);
    CHECK(diags[3].code == diag::ConstantConversion);
    CHECK(diags[4].code == diag::ArithOpMismatch);
    CHECK(diags[5].code == diag::ArithOpMismatch);
    CHECK(diags[6].code == diag::WidthExpand);
    CHECK(diags[7].code == diag::ArithOpMismatch);
}

TEST_CASE("case statement eval regression") {
    ScriptSession session;
    session.eval(R"(
function automatic int calc(int p);
    case (p)
        100,200:
            return 1;
        300:
            return 2;
    endcase
    return 0;
endfunction
)");

    CHECK(session.eval("calc(100);").integer() == 1);
    CHECK(session.eval("calc(200);").integer() == 1);
    CHECK(session.eval("calc(300);").integer() == 2);
    CHECK(session.eval("calc(400);").integer() == 0);
    NO_SESSION_ERRORS;
}

TEST_CASE("Array map eval") {
    ScriptSession session(optionsFor(LanguageVersion::v1800_2023));
    session.eval(R"(int A[] = {1,2,3}, B[3] = {2,3,5};)");
    session.eval(R"(real C[$] = {3.14};)");
    session.eval(R"(int D[string] = '{"Hello": -1, "World": 5};)");

    CHECK(session.eval("A.map with (item * 2.5)").toString() == "[2.5,5,7.5]");
    CHECK(session.eval("B.map with (1)").toString() == "[1,1,1]");
    CHECK(session.eval("C.map with (int'(item))").toString() == "[3]");
    CHECK(session.eval("D.map with (item * 3)").toString() == R"(["Hello":-3,"World":15])");

    NO_SESSION_ERRORS;
}

TEST_CASE("Packed struct field comparison const eval regress -- GH #1170") {
    auto tree = SyntaxTree::fromText(R"(
module m;
  typedef struct packed {
    int width;
  } t_config;

  parameter t_config Config = '{ width: 4 };
  parameter bit Compare = Config.width > -1;
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;

    auto& root = compilation.getRoot();
    auto& config = root.lookupName<ParameterSymbol>("m.Config");
    CHECK(config.getValue().integer() == 4);

    auto& compare = root.lookupName<ParameterSymbol>("m.Compare");
    CHECK(compare.getValue().integer() == 1);
}

TEST_CASE("Eval truthiness of strings") {
    ScriptSession session;
    session.eval(R"(
function automatic bit b;
    string s = "SDF";
    if (s)
        return 1;
    return 0;
endfunction
)");

    CHECK(session.eval("b()").integer() == 1);

    NO_SESSION_ERRORS;
}

TEST_CASE("Eval static cast type propagation") {
    ScriptSession session;
    CHECK(session.eval("(3)'(1'b1 << 2)").integer() == 4);
    CHECK(session.eval("int'(1'b1 + (1'b1 << 2))").integer() == 5);

    NO_SESSION_ERRORS;
}
