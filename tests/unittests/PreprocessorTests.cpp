#include "Test.h"

#include "slang/syntax/SyntaxPrinter.h"

std::string preprocess(string_view text, string_view name = "source", const Bag& options = {}) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics, options);
    preprocessor.pushSource(getSourceManager().assignText(name, text));

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

TEST_CASE("System include file") {
    auto& text = "`include <system.svh>";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "system stuff!");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Double include, no pragma once") {
    auto& text = R"(
`include "local.svh"
`include "local.svh"
)";
    auto& expected = R"(
// Just a test string
"test string"
// Just a test string
"test string"
)";

    std::string result = preprocess(text);
    result.erase(std::remove(result.begin(), result.end(), '\r'), result.end());

    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Double include, with pragma once") {
    auto& text = R"(
`include "include_once.svh"
`include "include_once.svh"
)";
    auto& expected = R"(
// Just a test string
"test string"
)";

    std::string result = preprocess(text);
    result.erase(std::remove(result.begin(), result.end(), '\r'), result.end());

    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Include directive errors") {
    auto& text = R"(
`include
`include < asdf . svh >
`include foo
`include ""
`include "include_once.svh"
)";

    PreprocessorOptions ppOptions;
    ppOptions.maxIncludeDepth = 0;

    Bag options;
    options.set(ppOptions);

    preprocess(text, "source", options);

    REQUIRE(diagnostics.size() == 5);
    CHECK(diagnostics[0].code == diag::CouldNotOpenIncludeFile);
    CHECK(diagnostics[1].code == diag::ExpectedIncludeFileName);
    CHECK(diagnostics[2].code == diag::ExpectedIncludeFileName);
    CHECK(diagnostics[3].code == diag::ExpectedIncludeFileName);
    CHECK(diagnostics[4].code == diag::ExceededMaxIncludeDepth);
}

void testDirective(SyntaxKind kind) {
    string_view text = LexerFacts::getDirectiveText(kind);

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
    testDirective(SyntaxKind::TimeScaleDirective);
    testDirective(SyntaxKind::UnconnectedDriveDirective);
    testDirective(SyntaxKind::UndefDirective);
    testDirective(SyntaxKind::UndefineAllDirective);

    CHECK(LexerFacts::getDirectiveText(SyntaxKind::Unknown) == "");
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
    CHECK(diagnostics.back().code == diag::UnknownDirective);
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

TEST_CASE("Function macro (apostrophe brace list in args)") {
    auto& text = "`define FOO(x) x\n`FOO('{a, b})";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::ApostropheOpenBrace);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Function macro (simple nesting)") {
    auto& text = "`define BLAHBLAH(x) x\n`define BAR(x) `BLAHBLAH(x)\n`define BAZ(x) "
                 "`BAR(x)\n`define FOO(y) `BAZ(y)\n`FOO(15)";
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

TEST_CASE("Macro pasting (weird)") {
    auto& text = "`define FOO(x) x``\\  \n`FOO(`)";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::Unknown);
    REQUIRE(diagnostics.size() == 2);
}

TEST_CASE("Macro pasting (weird 2)") {
    auto& text = "`define FOO(x,y) x``y  \n`FOO(a,)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "a");
    CHECK_DIAGNOSTICS_EMPTY;
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

TEST_CASE("Macro stringify useless concatenation") {
    auto& text = "`define FOO(x) `\"``x`\" \n`FOO(a)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "a");
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::IgnoredMacroPaste);
}

TEST_CASE("Macro define with missing paren") {
    auto& text = "`define FOO(asdf asdfasdf";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ExpectedToken);
}

TEST_CASE("Macro default with missing paren") {
    auto& text = "`define FOO(asdf= asdfasdf";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ExpectedToken);
}

TEST_CASE("Macro usage with missing paren") {
    auto& text = "`define FOO(asdf)\n`FOO(lkj ";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ExpectedToken);
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
    CHECK(diagnostics[0].code == diag::NotEnoughMacroArgs);
    CHECK(diagnostics[1].code == diag::NotEnoughMacroArgs);
    CHECK(diagnostics[2].code == diag::TooManyActualMacroArgs);
    CHECK(diagnostics[3].code == diag::NotEnoughMacroArgs);
    CHECK(diagnostics[4].code == diag::ExpectedMacroArgs);
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
    CHECK(diagnostics[0].code == diag::RecursiveMacro);
    CHECK(diagnostics[1].code == diag::RecursiveMacro);
}

TEST_CASE("Not recursive macros") {
    auto& text = R"(
`define A `B
`define B 1

`define FOO  `A `B
`FOO
)";

    preprocess(text);
    CHECK_DIAGNOSTICS_EMPTY;
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

TEST_CASE("Nested macro with different body locations") {
    auto& text = R"(
`define DEFINER(name, value) \
    `ifndef name \
        `define name (value) \
    `endif

`DEFINER(NESTED_DEFINE, 32 * 4)

`NESTED_DEFINE
)";
    auto& expected = "\n     \n         \n    \n(32 * 4)\n";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro arg location bug") {
    auto& text = R"(
`define FOO(name) name \

   `FOO(      `bar      )   asdfasdfasdfasdfasdfasdfsadfasdfasdfasdfasdf
)";
    auto& expected = R"(
      asdfasdfasdfasdfasdfasdfsadfasdfasdfasdfasdf
)";

    std::string result = preprocess(text);
    CHECK(result == expected);

    result = "\n" + reportGlobalDiags();
    CHECK(result == R"(
source:4:15: error: unknown macro or compiler directive '`bar'
   `FOO(      `bar      )   asdfasdfasdfasdfasdfasdfsadfasdfasdfasdfasdf
              ^
)");
}

TEST_CASE("Macro invalid argument handling") {
    auto& text = R"(
`define FOO(a) a
`define BAR(a) a
`define BAZ(=)
`define BOZ(a=(

`BAR(`FOO)
`BAR(`FOO(1, 2))
)";

    preprocess(text);

    REQUIRE(diagnostics.size() == 5);
    CHECK(diagnostics[0].code == diag::ExpectedIdentifier);
    CHECK(diagnostics[1].code == diag::UnbalancedMacroArgDims);
    CHECK(diagnostics[2].code == diag::ExpectedToken);
    CHECK(diagnostics[3].code == diag::ExpectedMacroArgs);
    CHECK(diagnostics[4].code == diag::TooManyActualMacroArgs);
}

TEST_CASE("Macro op outside define") {
    auto& text = R"(
asdf``llkj
foo \
bar
)";
    auto& expected = R"(
asdfllkj
foobar
)";

    std::string result = preprocess(text);
    CHECK(result == expected);

    REQUIRE(diagnostics.size() == 2);
    CHECK(diagnostics[0].code == diag::MacroOpsOutsideDefinition);
    CHECK(diagnostics[1].code == diag::MacroOpsOutsideDefinition);
}

TEST_CASE("Macro with line comment") {
    auto& text = R"(
`define FOO bar // hello
asdf

`FOO
)";
    auto& expected = R"(
 // hello
asdf
bar
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro with line comment with continuation") {
    auto& text = R"(
`define FOO bar // hello \
asdf

`FOO
)";
    auto& expected = R"(
bar // hello \
asdf
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro with block comment") {
    auto& text = R"(
`define FOO baz /* hello */ bar
`FOO
)";
    auto& expected = R"(
baz /* hello */ bar
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro with split block comment") {
    auto& text = R"(
`define FOO baz /* hel
lo */ bar
`FOO
)";
    auto& expected = R"(
 /* hel
lo */ bar
baz
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::SplitBlockCommentInDirective);
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
    auto& text = "`define FOO\n"
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
    auto& text = "`define FOO \\\n"
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

TEST_CASE("Ifdef error cases") {
    auto& text = R"(
`ifdef FOO
`else
`else
`endif

`endif
`else

`ifdef BAR
)";

    preprocess(text);

    REQUIRE(diagnostics.size() == 4);
    CHECK(diagnostics[0].code == diag::UnexpectedConditionalDirective);
    CHECK(diagnostics[1].code == diag::UnexpectedConditionalDirective);
    CHECK(diagnostics[2].code == diag::UnexpectedConditionalDirective);
    CHECK(diagnostics[3].code == diag::MissingEndIfDirective);
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
    auto& text = "`include \"local.svh\"\n"
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
    CHECK(token.valueText().substr(0, 15) == "<unnamed_buffer");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("FILE Directive (include+nesting)") {
    // file_uses_defn.svh includes file_defn.svh which has
    // `define FOO `__FILE__
    // and file_uses_defn.svh then has `FOO; that should expand to file_defn.svh
    // but when we expand FOO here, it shouldn't
    auto& text = "`include \"file_uses_defn.svh\"\n"
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
    auto& text = "`line 6 \"other.sv\" 0\n"
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

TEST_CASE("Invalid `line directive") {
    auto& text = "`line 6 \"other.sv\" 4";
    preprocess(text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::InvalidLineDirectiveLevel);
}

TEST_CASE("Coverage macros") {
    PreprocessorOptions ppOptions;
    Bag options;
    options.set(ppOptions);
    Preprocessor pp(getSourceManager(), alloc, diagnostics, options);

    CHECK(pp.isDefined("SV_COV_START"));
    CHECK(pp.isDefined("SV_COV_STOP"));
    CHECK(pp.isDefined("SV_COV_RESET"));
    CHECK(pp.isDefined("SV_COV_CHECK"));
    CHECK(pp.isDefined("SV_COV_MODULE"));
    CHECK(pp.isDefined("SV_COV_HIER"));
    CHECK(pp.isDefined("SV_COV_ASSERTION"));
    CHECK(pp.isDefined("SV_COV_FSM_STATE"));
    CHECK(pp.isDefined("SV_COV_STATEMENT"));
    CHECK(pp.isDefined("SV_COV_TOGGLE"));
    CHECK(pp.isDefined("SV_COV_OVERFLOW"));
    CHECK(pp.isDefined("SV_COV_ERROR"));
    CHECK(pp.isDefined("SV_COV_NOCOV"));
    CHECK(pp.isDefined("SV_COV_OK"));
    CHECK(pp.isDefined("SV_COV_PARTIAL"));

    auto& text = "`SV_COV_OK\n";
    Token token = lexToken(text);
    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("undef Directive") {
    auto& text = "`define FOO 45\n"
                 "`undef FOO\n"
                 "`FOO";
    Token token = lexToken(text);

    // The macro doesn't expand at all, so we go to end of file,
    // and there should be the error from the attempted expansion
    REQUIRE(token.kind == TokenKind::EndOfFile);
    CHECK(!diagnostics.empty());
}

TEST_CASE("undef Directive 2") {
    auto& text = "`define FOO 45\n"
                 "`FOO\n"
                 "`undef FOO\n";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.intValue() == 45);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("undefineall") {
    auto& text = "`define FOO 45\n"
                 "`undefineall\n"
                 "`FOO";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::EndOfFile);
    CHECK(!diagnostics.empty());
}

TEST_CASE("begin_keywords") {
    auto& text = "`begin_keywords \"1364-1995\"\n"
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
    auto& text = "`begin_keywords \"1800-2009\"\n"
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

optional<TimeScale> lexTimeScale(string_view text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);
    return preprocessor.getTimeScale();
}

TEST_CASE("timescale directive") {
    auto ts = lexTimeScale("`timescale 10 ns / 1 fs");
    CHECK_DIAGNOSTICS_EMPTY;
    REQUIRE(ts.has_value());
    CHECK(ts->base.magnitude == TimeScaleMagnitude::Ten);
    CHECK(ts->base.unit == TimeUnit::Nanoseconds);
    CHECK(ts->precision.magnitude == TimeScaleMagnitude::One);
    CHECK(ts->precision.unit == TimeUnit::Femtoseconds);

    ts = lexTimeScale("`timescale 100 s / 10ms");
    CHECK_DIAGNOSTICS_EMPTY;
    REQUIRE(ts.has_value());
    CHECK(ts->base.magnitude == TimeScaleMagnitude::Hundred);
    CHECK(ts->base.unit == TimeUnit::Seconds);
    CHECK(ts->precision.magnitude == TimeScaleMagnitude::Ten);
    CHECK(ts->precision.unit == TimeUnit::Milliseconds);

    ts = lexTimeScale("`timescale 1us/1ps");
    CHECK_DIAGNOSTICS_EMPTY;
    REQUIRE(ts.has_value());
    CHECK(ts->base.magnitude == TimeScaleMagnitude::One);
    CHECK(ts->base.unit == TimeUnit::Microseconds);
    CHECK(ts->precision.magnitude == TimeScaleMagnitude::One);
    CHECK(ts->precision.unit == TimeUnit::Picoseconds);

    lexTimeScale("`timescale 10fs / 100fs");
    CHECK(!diagnostics.empty());

    lexTimeScale("`timescale 10fs 100ns");
    CHECK(!diagnostics.empty());

    lexTimeScale("`timescale 1fs / 10us");
    CHECK(!diagnostics.empty());

    lexTimeScale("`timescale 1 bs / 2fs");
    CHECK(!diagnostics.empty());

    lexTimeScale("`timescale 1.2fs / 1fs");
    CHECK(!diagnostics.empty());
}

TokenKind lexDefaultNetType(string_view text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);
    return preprocessor.getDefaultNetType();
}

TEST_CASE("default_nettype directive") {
    CHECK(lexDefaultNetType("`default_nettype wire") == TokenKind::WireKeyword);
    CHECK(lexDefaultNetType("`default_nettype uwire") == TokenKind::UWireKeyword);
    CHECK(lexDefaultNetType("`default_nettype wand") == TokenKind::WAndKeyword);
    CHECK(lexDefaultNetType("`default_nettype wor") == TokenKind::WOrKeyword);
    CHECK(lexDefaultNetType("`default_nettype tri") == TokenKind::TriKeyword);
    CHECK(lexDefaultNetType("`default_nettype tri0") == TokenKind::Tri0Keyword);
    CHECK(lexDefaultNetType("`default_nettype tri1") == TokenKind::Tri1Keyword);
    CHECK(lexDefaultNetType("`default_nettype triand") == TokenKind::TriAndKeyword);
    CHECK(lexDefaultNetType("`default_nettype trior") == TokenKind::TriOrKeyword);
    CHECK(lexDefaultNetType("`default_nettype trireg") == TokenKind::TriRegKeyword);
    CHECK(lexDefaultNetType("`default_nettype none") == TokenKind::Unknown);
    CHECK_DIAGNOSTICS_EMPTY;

    CHECK(lexDefaultNetType("`default_nettype foo") == TokenKind::WireKeyword);
    CHECK(!diagnostics.empty());
    CHECK(lexDefaultNetType("`default_nettype module") == TokenKind::WireKeyword);
    CHECK(!diagnostics.empty());
}

TokenKind lexUnconnectedDrive(string_view text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);
    return preprocessor.getUnconnectedDrive();
}

TEST_CASE("unconnected_drive directive") {
    CHECK(lexUnconnectedDrive("`unconnected_drive pull0") == TokenKind::Pull0Keyword);
    CHECK(lexUnconnectedDrive("`unconnected_drive pull1") == TokenKind::Pull1Keyword);
    CHECK(lexUnconnectedDrive("`nounconnected_drive") == TokenKind::Unknown);
    CHECK_DIAGNOSTICS_EMPTY;

    CHECK(lexUnconnectedDrive("`unconnected_drive asdf") == TokenKind::Unknown);
    CHECK(!diagnostics.empty());
}

TEST_CASE("macro-defined include file") {
    auto& text = "`define FILE <include.svh>\n"
                 "`include `FILE";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "test string");
    CHECK_DIAGNOSTICS_EMPTY;

    auto& text2 = "`define FILE \"include.svh\"\n"
                  "`include `FILE";
    token = lexToken(text2);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "test string");
    CHECK_DIAGNOSTICS_EMPTY;

    auto& text3 = "`define FILE(arg) `\"arg`\"\n"
                  "`include `FILE(include.svh)";
    token = lexToken(text3);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "test string");
    CHECK_DIAGNOSTICS_EMPTY;

    auto& text4 = "`define FILE <includesh\n"
                  "`include `FILE";
    token = lexToken(text4);

    CHECK(!diagnostics.empty());
}

TEST_CASE("Preprocessor API") {
    PreprocessorOptions ppOptions;
    ppOptions.predefines.emplace_back("BAZ=4");
    ppOptions.predefines.emplace_back("BUZ");
    ppOptions.undefines.emplace_back("BUZ");

    Bag options;
    options.set(ppOptions);

    Preprocessor pp(getSourceManager(), alloc, diagnostics, options);
    CHECK(!pp.isDefined("FOO"));
    CHECK(pp.isDefined("__LINE__"));
    CHECK(!pp.undefine("FOO"));

    pp.predefine("FOO 1 2");
    CHECK(pp.isDefined("FOO"));
    CHECK(pp.undefine("FOO"));
    CHECK(!pp.isDefined("FOO"));
    CHECK(pp.isDefined("BAZ"));
    CHECK(!pp.isDefined("BUZ"));

    pp.setKeywordVersion(KeywordVersion::v1364_2001);
    CHECK(pp.getDefinedMacros().size() == 20);
}

TEST_CASE("Undef builtin") {
    auto& text = R"(
`undef __slang__
)";

    preprocess(text);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::UndefineBuiltinDirective);
}

TEST_CASE("Trying to redefine directive") {
    auto& text = R"(
`define timescale
)";

    preprocess(text);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::InvalidMacroName);
}

TEST_CASE("Trying to redefine built-in macro") {
    auto& text = R"(
`define __slang__
)";

    preprocess(text);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::InvalidMacroName);
}

TEST_CASE("Bad define directive") {
    auto& text = R"(
`define
)";

    preprocess(text);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ExpectedIdentifier);
}

TEST_CASE("Redefine macro -- same body") {
    auto& text = R"(
`define FOO(x, y     = 1+1) asdf bar   baz
`define FOO(x, y     = 1+1) asdf bar   baz
)";

    preprocess(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Redefine macro -- different bodies") {
    auto& text = R"(
`define FOO(x, y     = 1+1) asdf bar   baz
`define FOO(x, y     = 1   +1) asdf bar   baz
`define FOO(x, y     = 1   +1) asdf bar baz
`define FOO(x, y     = 1   +1) asdf bzr baz
`define FOO(x, y     = 1   +1) asdf baz
`define FOO(x, z, y     = 1   +1) asdf baz
`define FOO(x, z, y) asdf baz
`define FOO(x, z, y) asdf /**/ baz
`define FOO(x, z, b) asdf /**/ baz
`define FOO asdf /**/ baz
)";

    preprocess(text);
    REQUIRE(diagnostics.size() == 9);
    for (int i = 0; i < 9; i++) {
        CHECK(diagnostics[i].code == diag::RedefiningMacro);
    }
}

TEST_CASE("Macro stringify missing quote") {
    auto& text = R"(
`define FOO(a) `" a + b
`FOO(1)
)";

    preprocess(text);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ExpectedMacroStringifyEnd);
}

TEST_CASE("Pragma expressions") {
    auto& text = R"(
`pragma foo
`pragma bar asdf
`pragma bar 32 'd 1
`pragma bar 3.14159, foo=6.28
`pragma bar asdf='h ff, blah=2, foo="asdf", begin, bar=end
`pragma bar "asdf", (asdf, /* stuff */ "asdf", asdf="asdf")
`pragma reset protect
`pragma resetall
)";

    std::string result = preprocess(text);
    CHECK(result == "\n");

    for (auto& diag : diagnostics)
        CHECK(diag.code == diag::UnknownPragma);
}

TEST_CASE("Pragma expressions -- errors") {
    auto& text = R"(
`pragma
    foo

`pragma bar asdf=
    "asdf"

`pragma bar [

`pragma bar "asdf", (asdf, "asdf", asdf=[)
`pragma bar "asdf", (asdf, "asdf" asdf)
`pragma bar "asdf", (asdf, "asdf",
`pragma bar "asdf", (asdf, "asdf"
    )

`pragma bar 'h 3e+2
`pragma /* asdf
*/ asdf

`pragma reset (asdf, asdf), foo
`pragma resetall asdf, asdf
`pragma once asdf

`pragma protect begin
`pragma protect end
)";

    preprocess(text);

    std::string result = "\n" + reportGlobalDiags();
    CHECK(result == R"(
source:2:1: error: expected pragma name
`pragma
^
source:5:18: error: expected pragma expression
`pragma bar asdf=
                 ^
source:8:13: error: expected pragma expression
`pragma bar [
            ^
source:10:41: error: expected pragma expression
`pragma bar "asdf", (asdf, "asdf", asdf=[)
                                        ^
source:11:34: error: expected ','
`pragma bar "asdf", (asdf, "asdf" asdf)
                                 ^
source:13:34: error: expected ')'
`pragma bar "asdf", (asdf, "asdf"
                                 ^
source:12:35: error: expected ')'
`pragma bar "asdf", (asdf, "asdf",
                                  ^
source:11:9: warning: unknown pragma 'bar' [-Wunknown-pragma]
`pragma bar "asdf", (asdf, "asdf" asdf)
        ^~~
source:16:18: error: expected pragma expression
`pragma bar 'h 3e+2
                 ^
source:17:1: error: expected pragma name
`pragma /* asdf
^
source:16:9: warning: unknown pragma 'bar' [-Wunknown-pragma]
`pragma bar 'h 3e+2
        ^~~
source:25:9: warning: language feature not yet supported [-Wnot-supported]
`pragma protect end
        ^~~~~~~
source:24:9: warning: language feature not yet supported [-Wnot-supported]
`pragma protect begin
        ^~~~~~~
source:22:14: warning: too many arguments provided for pragma 'once' [-Wextra-pragma-args]
`pragma once asdf
             ^
source:21:18: warning: too many arguments provided for pragma 'resetall' [-Wextra-pragma-args]
`pragma resetall asdf, asdf
                 ^
source:20:15: error: expected pragma name
`pragma reset (asdf, asdf), foo
              ^~~~~~~~~~~~
source:20:29: warning: unknown pragma 'foo' [-Wunknown-pragma]
`pragma reset (asdf, asdf), foo
                            ^~~
)");
}

TEST_CASE("Pragma diagnostic errors") {
    auto& text = R"(
`pragma diagnostic
`pragma diagnostic foo
`pragma diagnostic 3'd3
`pragma diagnostic foo=3'd3
`pragma diagnostic ignore=3'd3
`pragma diagnostic ignore=foo
)";

    preprocess(text);

    REQUIRE(diagnostics.size() == 6);
    CHECK(diagnostics[0].code == diag::ExpectedDiagPragmaArg);
    CHECK(diagnostics[1].code == diag::ExpectedDiagPragmaArg);
    CHECK(diagnostics[2].code == diag::ExpectedDiagPragmaLevel);
    CHECK(diagnostics[3].code == diag::ExpectedDiagPragmaArg);
    CHECK(diagnostics[4].code == diag::UnknownDiagPragmaArg);
    CHECK(diagnostics[5].code == diag::ExpectedDiagPragmaArg);
}

TEST_CASE("Unknown function-like macro") {
    auto& text = R"(
`FOO(a, b)
bar
)";

    std::string result = preprocess(text);
    CHECK(result == "\nbar\n");
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::UnknownDirective);
}

TEST_CASE("celldefine check") {
    auto& text = R"(
`celldefine
module m;
endmodule
`endcelldefine
)";

    preprocess(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Non-macro replacement with backtick -- crash regress") {
    auto& text = R"(
`define FOO(a = `BAR) `a
`define BAR ,
`FOO(`BAR)
)";

    std::string result = preprocess(text);
    CHECK(result == "\n,\n");

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::MisplacedDirectiveChar);
}

TEST_CASE("Macro concat -- whitespace bug") {
    // Testing a regression:
    // This used to result in "xport_width" instead of "x port_width"
    auto& text = R"(
`define A(a) ``a``_width
`define B(b) b `A(``port``)
`B(x)
)";

    std::string result = preprocess(text);
    CHECK(result == "\nx port_width\n");
}

TEST_CASE("Macro concat into block comment") {
    // This is a silly thing that other tools support and real code in the wild
    // takes advantage of, so we must support it as well.
    auto& text = R"(
`define FFSR(__q, __d, __reset_value, __clk, __reset_clk) \
  `ifndef FOOBAR                                          \
  /``* synopsys sync_set_reset `"__reset_clk`" *``/       \
    `endif                                                \
  always_ff @(posedge (__clk)) begin                      \
    __q <= (__reset_clk) ? (__reset_value) : (__d);       \
  end

module m;
  logic q, d, clk, rst;
  `FFSR(q, d, 0, clk, rst)
endmodule
)";

    std::string result = preprocess(text);
    CHECK(result == R"(
module m;
  logic q, d, clk, rst;
  
                                            
  /* synopsys sync_set_reset "rst" */       
                                                    
  always_ff @(posedge (clk)) begin                      
    q <= (rst) ? (0) : (d);       
  end
endmodule
)");

    auto tree = SyntaxTree::fromText(text);
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Escaped macro with arguments") {
    auto& text = R"(
`define \quote (x)  `"`\`"x`\`"`"
module m;
  initial begin
    $display(`quote(text));
    $display(`\quote (text));
  end
endmodule
)";

    auto& expected = R"(
module m;
  initial begin
    $display("\"text\"");
    $display("\"text\"");
  end
endmodule
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Macro named with keyword") {
    auto& text = R"(
`define const const
`const
)";

    auto& expected = R"(
const
)";

    std::string result = preprocess(text);
    CHECK(result == expected);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Preproc stringify assertion regress GH #451") {
    auto& text = R"(
`define FOO (* instance_name = `"\inst_``NAME`" *)
`FOO
)";

    // Just test that no assert is hit.
    preprocess(text);
}

TEST_CASE("Macro inside an escaped identifier") {
    auto& text = R"(
`define MAKE_INST(NAME, SIG) \
    (* instance_name = `"inst_``NAME`" *) \
    mod \inst_``NAME (.sig(SIG));

module mod(input logic sig);
endmodule
module top;
    logic sig1, sig2;
    `MAKE_INST(A, sig1)
    `MAKE_INST(B, sig2)
endmodule
)";

    std::string result = preprocess(text);
    CHECK(result == R"(
module mod(input logic sig);
endmodule
module top;
    logic sig1, sig2;
    
    (* instance_name = "inst_A" *) 
    mod \inst_A  (.sig(sig1));
    
    (* instance_name = "inst_B" *) 
    mod \inst_B  (.sig(sig2));
endmodule
)");

    auto tree = SyntaxTree::fromText(text);
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Nested macro arg escaped identifier") {
    auto& text = R"(
`define FOO(a, b) a: b
`define BAR(a, b) `FOO(\asdf_``a , b)

module m;
    initial begin
        int i;
        `BAR([k]123, i++);
    end
endmodule
)";

    std::string result = preprocess(text);
    CHECK(result == R"(
module m;
    initial begin
        int i;
        \asdf_[k]123 : i++;
    end
endmodule
)");

    auto tree = SyntaxTree::fromText(text);
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Macro arg concat with multiple adjacent tokens") {
    auto& text = R"(
`define MACRO(ARG) \
    if (PARAM == 0) begin: size``ARG \
        assign var_``ARG = 1'b1; \
    end
module top #(
    int unsigned PARAM = 0
) ();
    logic var_4K;
    `MACRO(4K)
endmodule
)";

    std::string result = preprocess(text);
    CHECK(result == R"(
module top #(
    int unsigned PARAM = 0
) ();
    logic var_4K;
    
    if (PARAM == 0) begin: size4K 
        assign var_4K = 1'b1; 
    end
endmodule
)");

    auto tree = SyntaxTree::fromText(text);
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}

TEST_CASE("Macro defining new macro with newlines") {
    auto& text = R"(
`define FOO(x, y) \
    `ifndef x \
        `define x (y) \
    `endif
    
`FOO(baz,
    1 ?
        0 :
        1)

module m;
    int i = `baz;
endmodule
)";

    std::string result = preprocess(text);
    CHECK(result == R"(
    
     
         
    
module m;
    int i = (1 ?
        0 :
        1);
endmodule
)");

    auto tree = SyntaxTree::fromText(text);
    Compilation compilation;
    compilation.addSyntaxTree(tree);
    NO_COMPILATION_ERRORS;
}
