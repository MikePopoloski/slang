#include "Test.h"

#include "slang/compilation/ScriptSession.h"

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
}

TEST_CASE("Eval for loop") {
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

    // Bit selects
    EVAL("3'd7[2]", 1);
    EVAL("5'd25[3:0]", 9);
    EVAL("5'd25[3:1]", 4);
    EVAL("65'h1ffffffffffffffff[64:62]", "3'b111"_si);
    EVAL("5'd25[0 +: 4]", 9);
    EVAL("5'd25[3 -: 4]", 9);

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

TEST_CASE("dimension based system functions") {
    ScriptSession session;
    session.eval("logic [0 : 15] up_vect = 5'b10111;");
    session.eval("logic [15 : 0] down_vect = 5'd25;");

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
    session.eval("function int foo(int a); return f + a; endfunction");
    session.eval("function int bar(int b); return foo(b + 1); endfunction");

    CHECK(!session.eval("localparam int p = bar(1);"));

    std::string msg = "\n" + report(session.getDiagnostics());
    CHECK(msg == R"(
source:1:20: error: expression is not constant
localparam int p = bar(1);
                   ^~~~~~
source:1:33: note: all identifiers that are not parameters must be declared locally to a constant function
function int foo(int a); return f + a; endfunction
                                ^
source:1:33: note: in call to 'foo'
function int bar(int b); return foo(b + 1); endfunction
                                ^
source:1:20: note: in call to 'bar'
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

    auto cv = session.eval("arr");
    CHECK(cv.elements()[7].integer() == 42);
    CHECK(cv.elements()[6].integer() == 1234);
    CHECK(cv.elements()[5].integer() == 19);

    CHECK(session.eval("arr[1:2] == arr2").integer() == 1);

    cv = session.eval("1 ? arr[1:2] : arr2");
    CHECK(cv.elements()[1].integer() == 1234);
    CHECK(cv.elements()[0].integer() == 19);

    cv = session.eval("'x ? arr[1:2] : arr2");
    CHECK(cv.elements()[1].integer() == 1234);
    CHECK(cv.elements()[0].integer() == 19);

    session.eval("arr2[0] = 1;");
    cv = session.eval("'x ? arr[1:2] : arr2");
    CHECK(cv.elements()[1].integer() == 0);
    CHECK(cv.elements()[0].integer() == 19);

    NO_SESSION_ERRORS;
}

TEST_CASE("Unpacked struct eval") {
    ScriptSession session;
    session.eval("struct { integer a[2:0]; bit b; } foo;");
    session.eval("foo.a[0] = 42;");
    session.eval("foo.b = 1;");

    auto cv = session.eval("foo");
    CHECK(cv.elements()[0].elements()[0].integer() == 42);

    CHECK(session.eval("foo.a[0] == 42").integer() == 1);
    CHECK_THAT(session.eval("foo == foo").integer(), exactlyEquals(SVInt(logic_t::x)));
    CHECK(session.eval("foo === foo").integer() == 1);

    NO_SESSION_ERRORS;
}

TEST_CASE("String literal ops") {
    ScriptSession session;
    session.eval("bit [8*14:1] str;");

    SVInt v = session.eval("str = \"Hello world\";").integer();
    CHECK(v == "112'h48656c6c6f20776f726c64"_si);

    v = session.eval("str = {str, \"!!!\"};").integer();
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

    NO_SESSION_ERRORS;
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
}

TEST_CASE("Eval sformatf") {
    ScriptSession session;
    session.eval("logic [125:0] foo = '0;");
    session.eval("logic signed [125:0] bar = '1;");
    session.eval("logic signed [125:0] baz = 1;");

    auto sformatf = [&](auto str, auto args) {
        return session.eval("$sformatf(\""s + str + "\", " + args + ")").str();
    };

    CHECK(sformatf("", "") == "");
    CHECK(sformatf("%d", "foo") == "                                     0");
    CHECK(sformatf("%0d", "foo") == "0");
    CHECK(sformatf("%2D", "foo") == " 0");
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

    CHECK(sformatf("%s", "\"abc\"") == "abc");
    CHECK(sformatf("%3s", "\"a\"") == "  a");
    CHECK(sformatf("%3s", "\"abc\"") == "abc");
    CHECK(sformatf("%3s", "\"abcdef\"") == "abcdef");

    CHECK(sformatf("%c", "48") == "0");
    CHECK(sformatf("%c", "18'hx031") == "1");
    CHECK(sformatf("%c", "999") == "\xe7");

    CHECK(sformatf("%m", "") == "$unit");

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
}

TEST_CASE("Concat assignments") {
    ScriptSession session;
    session.eval("logic [2:0] foo;");
    session.eval("logic bar;");

    session.eval("{bar, foo} = 3'b111 + 2'd3");
    NO_SESSION_ERRORS;

    CHECK(session.eval("bar").integer() == 1);
    CHECK(session.eval("foo").integer() == 2);
}