#include "Test.h"

#include "slang/syntax/SyntaxPrinter.h"

std::string preprocess(string_view text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    std::string result;
    while (true) {
        Token token = preprocessor.next();
        result += token.toString();
        if (token.kind == TokenKind::EndOfFile)
            break;
    }

    return result;
}

TEST_CASE("Include File") {
    auto& text = "`include \"include.svh\"";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "test string");
    CHECK_DIAGNOSTICS_EMPTY;
}

void testDirective(SyntaxKind kind) {
    string_view text = getDirectiveText(kind);

    diagnostics.clear();
    auto buffer = getSourceManager().assignText(text);
    Lexer lexer(buffer, alloc, diagnostics);

    Token token = lexer.lex();
    REQUIRE(token);

    CHECK(token.kind == TokenKind::Directive);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Directives") {
    testDirective(SyntaxKind::BeginKeywordsDirective);
    testDirective(SyntaxKind::CellDefineDirective);
    testDirective(SyntaxKind::DefaultNetTypeDirective);
    testDirective(SyntaxKind::DefineDirective);
    testDirective(SyntaxKind::ElseDirective);
    testDirective(SyntaxKind::ElsIfDirective);
    testDirective(SyntaxKind::EndKeywordsDirective);
    testDirective(SyntaxKind::EndCellDefineDirective);
    testDirective(SyntaxKind::EndIfDirective);
    testDirective(SyntaxKind::IfDefDirective);
    testDirective(SyntaxKind::IfNDefDirective);
    testDirective(SyntaxKind::IncludeDirective);
    testDirective(SyntaxKind::LineDirective);
    testDirective(SyntaxKind::NoUnconnectedDriveDirective);
    testDirective(SyntaxKind::PragmaDirective);
    testDirective(SyntaxKind::ResetAllDirective);
    testDirective(SyntaxKind::TimescaleDirective);
    testDirective(SyntaxKind::UnconnectedDriveDirective);
    testDirective(SyntaxKind::UndefDirective);
    testDirective(SyntaxKind::UndefineAllDirective);

    CHECK(getDirectiveText(SyntaxKind::Unknown) == "");
}

TEST_CASE("Macro define (simple)") {
    auto& text = "`define FOO (1)";
    Token token = lexToken(text);

    std::string str = SyntaxPrinter().setIncludeDirectives(true).print(token).str();

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(str == text);
    CHECK_DIAGNOSTICS_EMPTY;
    REQUIRE(token.trivia().size() == 1);
    REQUIRE(token.trivia()[0].kind == TriviaKind::Directive);

    const auto& def = token.trivia()[0].syntax()->as<DefineDirectiveSyntax>();
    CHECK(def.name.valueText() == "FOO");
    CHECK(def.directive);
    CHECK(!def.formalArguments);
    REQUIRE(def.body.size() == 3);
    CHECK(def.body[1].kind == TokenKind::IntegerLiteral);
}

TEST_CASE("Macro define (function-like)") {
    auto& text = "`define FOO(a) a+1";
    Token token = lexToken(text);

    std::string str = SyntaxPrinter().setIncludeDirectives(true).print(token).str();

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(str == text);
    CHECK_DIAGNOSTICS_EMPTY;
    REQUIRE(token.trivia().size() == 1);
    REQUIRE(token.trivia()[0].kind == TriviaKind::Directive);

    const auto& def = token.trivia()[0].syntax()->as<DefineDirectiveSyntax>();
    CHECK(def.name.valueText() == "FOO");
    CHECK(def.directive);
    REQUIRE(def.formalArguments);
    CHECK(def.formalArguments->args.size() == 1);
    CHECK(def.formalArguments->args[0]->name.valueText() == "a");
    REQUIRE(def.body.size() == 3);
    CHECK(def.body[2].kind == TokenKind::IntegerLiteral);
}

TEST_CASE("Macro usage (undefined)") {
    auto& text = "`FOO";
    lexToken(text);

    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == DiagCode::UnknownDirective);
}

TEST_CASE("Macro usage (simple)") {
    auto& text = "`define FOO 42\n`FOO";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 42);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Function macro (simple)") {
    auto& text = "`define FOO(x) x\n`FOO(3)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 3);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Function macro (defaults)") {
    auto& text = "`define FOO(x=9(,), y=2) x\n`FOO()";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 9);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Function macro (no tokens)") {
    auto& text = "`define FOO(x=) x\n`FOO()";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::EndOfFile);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Function macro (simple nesting)") {
    auto& text = "`define BLAHBLAH(x) x\n`define BAR(x) `BLAHBLAH(x)\n`define BAZ(x) `BAR(x)\n`define FOO(y) `BAZ(y)\n`FOO(15)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 15);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Function macro (arg nesting)") {
    auto& text = "`define FOO(x) x\n`FOO(`FOO(3))";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 3);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Function macro (keyword as formal argument)") {
    auto& text = "`define FOO(type) type\n`FOO(3)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 3);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro pasting (identifiers)") {
    auto& text = "`define FOO(x,y) x``_blah``y\n`FOO(   bar,    _BAZ)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "bar_blah_BAZ");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro pasting (operator)") {
    auto& text = "`define FOO(x) x``+\n`FOO(+)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::DoublePlus);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro pasting (combination)") {
    auto& text = "`define FOO(x,y) x``foo``y``42\n`FOO(bar_, 32)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "bar_foo3242");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro pasting (keyword)") {
    auto& text = "`define FOO(x) x``gic\n`FOO(lo)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::LogicKeyword);
    CHECK(token.valueText() == "logic");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro pasting (mixed)") {
    auto& text = "`define FOO(x) ;``x\n`FOO(y)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::Semicolon);
    CHECK(token.valueText() == ";");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro pasting (whitespace)") {
    auto& text = "`define FOO(x) x`` y\n`FOO(a)";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "a");
    REQUIRE(diagnostics.size() == 1);
}

TEST_CASE("Macro stringify") {
    auto& text = "`define FOO(x) `\" `\\`\" x``foo``42 `\\`\" `\"\n`FOO(bar_)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == " \" bar_foo42 \"");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro stringify whitespace") {
    auto& text = "`define FOO(x,y) `\" x ( y)\t  x   x`\"\n`FOO(bar,)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == " bar ( )\t  bar   bar");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro define with missing paren") {
    auto& text = "`define FOO(asdf asdfasdf";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == DiagCode::ExpectedToken);
}

TEST_CASE("Macro default with missing paren") {
    auto& text = "`define FOO(asdf= asdfasdf";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == DiagCode::ExpectedToken);
}

TEST_CASE("Macro usage with missing paren") {
    auto& text = "`define FOO(asdf)\n`FOO(lkj ";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == DiagCode::ExpectedToken);
}

TEST_CASE("Macro deferred define") {
    auto& text = R"(
`define DEFIF_DEFNOT(d, a) \
    `undef d \
    `ifndef a \
        `DEFINEIT(`define d 1) \
    `endif

`define DEFINEIT(d) d \

// BAR is not define, so FOO should be
`DEFIF_DEFNOT(FOO, BAR)

`FOO
)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 1);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro string expansions") {
    // These examples were all pulled from the spec.
    auto& text = R"(
`define D(x,y) initial $display("start", x , y, "end");
`define MACRO1(a=5,b="B",c) $display(a,,b,,c);
`define MACRO2(a=5, b, c="C") $display(a,,b,,c);
`define MACRO3(a=5, b=0, c="C") $display(a,,b,,c);

`D( "msg1" , "msg2" )
`D( " msg1", )
`D(, "msg2 ")
`D(,)
`D(  ,  )
`D("msg1")
`D()
`D(,,)

`MACRO1 ( , 2, 3 )
`MACRO1 ( 1 , , 3 )
`MACRO1 ( , 2, )
`MACRO1 ( 1 )

`MACRO2 (1, , 3)
`MACRO2 (, 2, )
`MACRO2 (, 2)

`MACRO3 ( 1 )
`MACRO3 ( )
`MACRO3
)";

    auto& expected = R"(
initial $display("start", "msg1" , "msg2", "end");
initial $display("start", " msg1" , , "end");
initial $display("start",  , "msg2 ", "end");
initial $display("start",  , , "end");
initial $display("start",  , , "end");
$display(5,,2,,3);
$display(1,,"B",,3);
$display(5,,2,,);
$display(1,,,,3);
$display(5,,2,,"C");
$display(5,,2,,"C");
$display(1,,0,,"C");
$display(5,,0,,"C");
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    REQUIRE(diagnostics.size() == 5);
    CHECK(diagnostics[0].code == DiagCode::NotEnoughMacroArgs);
    CHECK(diagnostics[1].code == DiagCode::NotEnoughMacroArgs);
    CHECK(diagnostics[2].code == DiagCode::TooManyActualMacroArgs);
    CHECK(diagnostics[3].code == DiagCode::NotEnoughMacroArgs);
    CHECK(diagnostics[4].code == DiagCode::ExpectedMacroArgs);
}

TEST_CASE("Macro string expansions 2") {
    // These examples were all pulled from the spec.
    auto& text = R"(
`define max(a,b)((a) > (b)) ? (a) : (b)
`define msg(x,y) `"x: `\`"y`\`"`"
`define TOP(a,b) a + b

n = `max(p+q, r+s) ;
`TOP( `TOP(b,1), `TOP(42,a) )
$display(`msg(left side,right side));
)";

    auto& expected = R"(
n = ((p+q) > (r+s)) ? (p+q) : (r+s) ;
b + 1 + 42 + a
$display("left side: \"right side\"");
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro string expansions 3") {
    auto& text = R"**(
`define MACRO(a="==)", b = "((((", c = () ) a b c
`MACRO()

`define FOO(a, b) a b
`FOO(asdf, blah[1,2,3])

`define JOIN(a,b) `"a``b``\n`"`"asdf\n`"123foo
`JOIN(a1,b2)
)**";

    auto& expected = R"**(
"==)" "((((" ()
asdf blah[1,2,3]
"a1b2\n""asdf\n"123foo
)**";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro meta repetition") {
    auto& text = R"(
`define REPEAT(n, d) `REPEAT_``n(d)
`define REPEAT_0(d)
`define REPEAT_1(d) d
`define REPEAT_2(d) `REPEAT_1(d) d
`define REPEAT_3(d) `REPEAT_2(d) d
`define REPEAT_4(d) `REPEAT_3(d) d

`define FUNC(n) n

`REPEAT(`FUNC(4), "hello")
)";

    auto& expected = R"(
"hello" "hello" "hello" "hello"
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro nested stringification") {
    auto& text = R"(
`define THRU(d) d
`define MSG(m) `"m`"

$display(`MSG(`THRU(hello)))
)";

    auto& expected = R"(
$display("hello")
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro nested multiline stringification") {
    auto& text = R"(
`define MULTILINE line1 \
line2

`define MSG(m) `"m`"

$display(`MSG(`MULTILINE))
)";

    auto& expected = R"(
$display("line1 line2")
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro indirect ifdef branch") {
    auto& text = R"(
`define DEFINED
`define INDIRECT(d) d
`ifdef `INDIRECT(DEFINED)
a
`else
b
`endif
)";

    auto& expected = "\na\n";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro directive token substitution via arg") {
    auto& text = R"(
`define FOO 1
`define FROB(asdf) `asdf

`FROB(FOO)
)";

    auto& expected = R"(
1
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro bonkers arg substitution") {
    auto& text = R"(
`define FROB(asdf) `asdf STUFF 1
`FROB(define)

`STUFF
)";

    auto& expected = R"(
1
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Recursive macros") {
    auto& text = R"(
`define A `A 1
`A

`define FOO(a) `BA``a
`define BAR `FOO(R)
`define ARG R

`FOO(`ARG)
)";

    preprocess(text);
    REQUIRE(diagnostics.size() == 2);
    CHECK(diagnostics[0].code == DiagCode::RecursiveMacro);
    CHECK(diagnostics[1].code == DiagCode::RecursiveMacro);
}

TEST_CASE("Unknown macro as arg not an error") {
    auto& text = R"(
`define FOO(a) foo
`FOO(`BAZ)
)";
    auto& expected = R"(
foo
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Two expansions of same macro") {
    auto& text = R"(
`define FOO foo
`define BAR `FOO `FOO
`BAR

`define BAZ(a) a
`BAZ(`FOO`FOO)
)";
    auto& expected = R"(
foo foo
foofoo
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro with escaped name") {
    auto& text = R"(
`define \FOO foo
`ifdef \FOO
`\FOO
`endif
)";
    auto& expected = R"(
foo
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("IfDef branch (taken)") {
    auto& text = "`define FOO\n`ifdef FOO\n42\n`endif";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 42);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("IfDef branch (not taken)") {
    auto& text = "`define FOO\n`ifdef BAR\n42\n`endif";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("IfNDef branch") {
    auto& text = "`ifndef BAR\n42\n`endif";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 42);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("ElseIf branch") {
    auto& text = "`define FOO\n`ifdef BAR\n42\n`elsif FOO\n99`else\n1000`endif";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 99);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("EndIf not done") {
    auto& text = "`ifdef FOO\n`ifdef BAR\n42\n`endif\n1000\n`endif\n42.3";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::RealLiteral);
    CHECK(token.realValue() == 42.3);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Ifdef same line") {
    auto& text = "`ifndef BLAH 1000 `endif";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 1000);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Nested branches") {
    auto& text =
"`define FOO\n"
"`ifdef BLAH\n"
"   `define BAZ\n"
"`elsif BAZ\n"
"   42\n"
"`else\n"
"   `define YEP\n"
"   `ifdef YEP\n"
"       `ifdef FOO\n"
"           `ifdef NOPE1\n"
"               blahblah\n"
"           `elsif NOPE2\n"
"               blahblah2\n"
"           `elsif YEP\n"
"               `ifdef FOO\n"
"                   99\n"
"               `endif\n"
"           `endif\n"
"       `endif\n"
"   `endif\n"
"`endif";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 99);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("IfDef inside macro") {
    auto& text =
"`define FOO \\\n"
"  `ifdef BAR \\\n"
"    32 \\\n"
"  `else \\\n"
"    63 \\\n"
"  `endif \\\n"
"\n"
"`define BAR\n"
"`FOO";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 32);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Nested ifdef and macros") {
    auto& text = R"(
`define stuff asdfasdf
`define FOO \
    `ifdef NEVER \
        `blahblah \
    `else \
        `stuff \
    `endif
`FOO
)";
    auto& expected = "\n     \n     \n        asdfasdf \n    \n";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("LINE Directive") {
    auto& text = "`__LINE__";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 1);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("LINE Directive as actual arg") {
    auto& text = "`define FOO(x) x\n`define BAR `FOO(`__LINE__)\n`BAR";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 3);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("LINE Directive (include+nesting)") {
    auto& text =
"`include \"local.svh\"\n"
"`define BAZ `__LINE__\n"
"`define BAR `BAZ\n"
"`define FOO `BAR\n"
"`FOO";
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    // Get the second token, the first token is the test string from the includes
    Token token = preprocessor.next();
    token = preprocessor.next();
    REQUIRE(token);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 5);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("FILE Directive") {
    auto& text = "`__FILE__";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::StringLiteral);
    // we set the name by default for files created this way as
    // <unnamed_bufferN> for some N, let's not be sensitive to that number
    CHECK(token.valueText().substr(0,15) == "<unnamed_buffer");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("FILE Directive (include+nesting)") {
    // file_uses_defn.svh includes file_defn.svh which has
    // `define FOO `__FILE__
    // and file_uses_defn.svh then has `FOO; that should expand to file_defn.svh
    // but when we expand FOO here, it shouldn't
    auto& text =
"`include \"file_uses_defn.svh\"\n"
"`BAR";

    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);

    std::string compare = fs::proximate(findTestDir() + "/file_uses_defn.svh").string();

    REQUIRE(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == compare);

    token = preprocessor.next();
    REQUIRE(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() != compare);

    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("`line + FILE + LINE Directive") {
    auto& text =
"`line 6 \"other.sv\" 0\n"
"`__LINE__\n"
"`include \"file_uses_defn.svh\"\n"
"`__FILE__";

    diagnostics.clear();
    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 6);

    token = preprocessor.next();
    REQUIRE(token.kind == TokenKind::StringLiteral);
    std::string compare = fs::proximate(findTestDir() + "/file_uses_defn.svh").string();
    CHECK(token.valueText() == compare);

    token = preprocessor.next();
    REQUIRE(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "other.sv");

    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("undef Directive") {
    auto& text =
"`define FOO 45\n"
"`undef FOO\n"
"`FOO";
    Token token = lexToken(text);

    // The macro doesn't expand at all, so we go to end of file,
    // and there should be the error from the attempted expansion
    REQUIRE(token.kind == TokenKind::EndOfFile);
    CHECK(!diagnostics.empty());
}

TEST_CASE("undef Directive 2") {
    auto& text =
"`define FOO 45\n"
"`FOO\n"
"`undef FOO\n";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 45);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("undefineall") {
    auto& text =
"`define FOO 45\n"
"`undefineall\n"
"`FOO";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::EndOfFile);
    CHECK(!diagnostics.empty());
}

TEST_CASE("begin_keywords") {
    auto& text =
"`begin_keywords \"1364-1995\"\n"
"soft\n"
"`end_keywords\n"
"soft";
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);

    REQUIRE(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "soft");

    token = preprocessor.next();
    REQUIRE(token.kind == TokenKind::SoftKeyword);

    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("begin_keywords (nested)") {
    auto& text =
"`begin_keywords \"1800-2009\"\n"
"`begin_keywords \"1800-2005\"\n"
"`begin_keywords \"1364-2001\"\n"
"uwire\n"
"`end_keywords\n"
"uwire\n"
"`end_keywords\n"
"`end_keywords\n";
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);

    REQUIRE(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "uwire");

    token = preprocessor.next();
    REQUIRE(token.kind == TokenKind::UWireKeyword);

    CHECK_DIAGNOSTICS_EMPTY;
}

optional<Timescale> lexTimescale(string_view text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);
    return preprocessor.getTimescale();
}

TEST_CASE("timescale directive") {
    auto ts = lexTimescale("`timescale 10 ns / 1 fs");
    CHECK_DIAGNOSTICS_EMPTY;
    REQUIRE(ts.has_value());
    CHECK(ts->base.magnitude == TimescaleMagnitude::Ten);
    CHECK(ts->base.unit == TimeUnit::Nanoseconds);
    CHECK(ts->precision.magnitude == TimescaleMagnitude::One);
    CHECK(ts->precision.unit == TimeUnit::Femtoseconds);

    ts = lexTimescale("`timescale 100 s / 10ms");
    CHECK_DIAGNOSTICS_EMPTY;
    REQUIRE(ts.has_value());
    CHECK(ts->base.magnitude == TimescaleMagnitude::Hundred);
    CHECK(ts->base.unit == TimeUnit::Seconds);
    CHECK(ts->precision.magnitude == TimescaleMagnitude::Ten);
    CHECK(ts->precision.unit == TimeUnit::Milliseconds);

    ts = lexTimescale("`timescale 1us/1ps");
    CHECK_DIAGNOSTICS_EMPTY;
    REQUIRE(ts.has_value());
    CHECK(ts->base.magnitude == TimescaleMagnitude::One);
    CHECK(ts->base.unit == TimeUnit::Microseconds);
    CHECK(ts->precision.magnitude == TimescaleMagnitude::One);
    CHECK(ts->precision.unit == TimeUnit::Picoseconds);

    lexTimescale("`timescale 10fs / 100fs");
    CHECK(!diagnostics.empty());

    lexTimescale("`timescale 10fs 100ns");
    CHECK(!diagnostics.empty());

    lexTimescale("`timescale 1fs / 10us");
    CHECK(!diagnostics.empty());

    lexTimescale("`timescale 1 bs / 2fs");
    CHECK(!diagnostics.empty());

    lexTimescale("`timescale 1.2fs / 1fs");
    CHECK(!diagnostics.empty());
}

TEST_CASE("macro-defined include file") {
    auto& text =
"`define FILE <include.svh>\n"
"`include `FILE";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "test string");
    CHECK_DIAGNOSTICS_EMPTY;

    auto& text2 =
"`define FILE \"include.svh\"\n"
"`include `FILE";
    token = lexToken(text2);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "test string");
    CHECK_DIAGNOSTICS_EMPTY;

    auto& text3 =
"`define FILE(arg) `\"arg`\"\n"
"`include `FILE(include.svh)";
    token = lexToken(text3);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "test string");
    CHECK_DIAGNOSTICS_EMPTY;


    auto& text4 =
"`define FILE <includesh\n"
"`include `FILE";
    token = lexToken(text4);

    CHECK(!diagnostics.empty());
}

TEST_CASE("Preprocessor API") {
    Preprocessor pp(getSourceManager(), alloc, diagnostics);
    CHECK(!pp.isDefined("FOO"));
    CHECK(pp.isDefined("__LINE__"));
    CHECK(!pp.undefine("FOO"));

    pp.predefine("FOO");
    CHECK(pp.isDefined("FOO"));
    CHECK(pp.undefine("FOO"));
    CHECK(!pp.isDefined("FOO"));
}