#include "Catch/catch.hpp"

#include "lexing/Preprocessor.h"
#include "parsing/AllSyntax.h"
#include "text/SourceManager.h"

using namespace slang;

namespace {

BumpAllocator alloc;
Diagnostics diagnostics;

SourceManager& getSourceManager() {
    static SourceManager* sourceManager = nullptr;
    if (!sourceManager) {
        auto path = Path::getCurrentDirectory();
        while (!(path + "tests").exists()) {
            path = path.parentPath();
            ASSERT(!path.empty(), "Failed to find root project directory");
        }
        
        auto pathStr = (path + "tests/unittests/data/").str();
        sourceManager = new SourceManager();
        sourceManager->addUserDirectory(StringRef(pathStr));
    }
    return *sourceManager;
}

// A helper for when tests break and you want to see the diagnostics
void logDiagnostics() {
    for (auto& diag : diagnostics) {
        fprintf(stderr, "%s\n", DiagnosticWriter(getSourceManager()).report(diag).c_str());
    }
}

Token lexToken(StringRef text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);
    return token;
}

std::string preprocess(StringRef text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    std::string result;
    while (true) {
        Token token = preprocessor.next();
        result += token.toString(SyntaxToStringFlags::IncludePreprocessed | SyntaxToStringFlags::IncludeTrivia);
        if (token.kind == TokenKind::EndOfFile)
            break;
    }

    return result;
}

TEST_CASE("Include File", "[preprocessor]") {
    auto& text = "`include \"include.svh\"";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "test string");
    CHECK(diagnostics.empty());
}

void testDirective(SyntaxKind kind) {
    StringRef text = getDirectiveText(kind);

    diagnostics.clear();
    auto buffer = getSourceManager().assignText(text);
    Lexer lexer(buffer, alloc, diagnostics);

    Token token = lexer.lex(LexerMode::Directive);
    REQUIRE(token);

    CHECK(token.kind == TokenKind::Directive);
    CHECK(token.toString(SyntaxToStringFlags::IncludeTrivia) == text);
    CHECK(token.valueText() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Directives", "[preprocessor]") {
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
}

TEST_CASE("Macro define (simple)", "[preprocessor]") {
    auto& text = "`define FOO (1)";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString(SyntaxToStringFlags::IncludeTrivia | SyntaxToStringFlags::IncludeDirectives) == text);
    CHECK(diagnostics.empty());
    REQUIRE(token.trivia().count() == 1);
    REQUIRE(token.trivia()[0].kind == TriviaKind::Directive);

    const auto& def = token.trivia()[0].syntax()->as<DefineDirectiveSyntax>();
    CHECK(def.name.valueText() == "FOO");
    CHECK(def.endOfDirective);
    CHECK(def.directive);
    CHECK(!def.formalArguments);
    REQUIRE(def.body.count() == 3);
    CHECK(def.body[1].kind == TokenKind::IntegerLiteral);
}

TEST_CASE("Macro define (function-like)", "[preprocessor]") {
    auto& text = "`define FOO(a) a+1";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString(SyntaxToStringFlags::IncludeTrivia | SyntaxToStringFlags::IncludeDirectives) == text);
    CHECK(diagnostics.empty());
    REQUIRE(token.trivia().count() == 1);
    REQUIRE(token.trivia()[0].kind == TriviaKind::Directive);

    const auto& def = token.trivia()[0].syntax()->as<DefineDirectiveSyntax>();
    CHECK(def.name.valueText() == "FOO");
    CHECK(def.endOfDirective);
    CHECK(def.directive);
    CHECK(def.formalArguments);
    CHECK(def.formalArguments->args.count() == 1);
    CHECK(def.formalArguments->args[0]->name.valueText() == "a");
    REQUIRE(def.body.count() == 3);
    CHECK(def.body[2].kind == TokenKind::IntegerLiteral);
}

TEST_CASE("Macro usage (undefined)", "[preprocessor]") {
    auto& text = "`FOO";
    Token token = lexToken(text);

    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == DiagCode::UnknownDirective);
}

TEST_CASE("Macro usage (simple)", "[preprocessor]") {
    auto& text = "`define FOO 42\n`FOO";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(std::get<SVInt>(token.numericValue()) == 42);
    CHECK(diagnostics.empty());
}

TEST_CASE("Function macro (simple)", "[preprocessor]") {
    auto& text = "`define FOO(x) x\n`FOO(3)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(std::get<SVInt>(token.numericValue()) == 3);
    CHECK(diagnostics.empty());
}

TEST_CASE("Function macro (defaults)", "[preprocessor]") {
    auto& text = "`define FOO(x=9(,), y=2) x\n`FOO()";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(std::get<SVInt>(token.numericValue()) == 9);
    CHECK(diagnostics.empty());
}

TEST_CASE("Function macro (no tokens)", "[preprocessor]") {
    auto& text = "`define FOO(x=) x\n`FOO()";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::EndOfFile);
    CHECK(diagnostics.empty());
}

TEST_CASE("Function macro (simple nesting)", "[preprocessor]") {
    auto& text = "`define BLAHBLAH(x) x\n`define BAR(x) `BLAHBLAH(x)\n`define BAZ(x) `BAR(x)\n`define FOO(y) `BAZ(y)\n`FOO(15)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(std::get<SVInt>(token.numericValue()) == 15);
    CHECK(diagnostics.empty());
}

TEST_CASE("Function macro (arg nesting)", "[preprocessor]") {
    auto& text = "`define FOO(x) x\n`FOO(`FOO(3))";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(std::get<SVInt>(token.numericValue()) == 3);
    CHECK(diagnostics.empty());
}

TEST_CASE("Function macro (keyword as formal argument)", "[preprocessor]") {
    auto& text = "`define FOO(type) type\n`FOO(3)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(std::get<SVInt>(token.numericValue()) == 3);
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro pasting (identifiers)", "[preprocessor]") {
    auto& text = "`define FOO(x,y) x``_blah``y\n`FOO(   bar,    _BAZ)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "bar_blah_BAZ");
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro pasting (operator)", "[preprocessor]") {
    auto& text = "`define FOO(x) x``+\n`FOO(+)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::DoublePlus);
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro pasting (combination)", "[preprocessor]") {
    auto& text = "`define FOO(x,y) x``foo``y``42\n`FOO(bar_, 32)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "bar_foo3242");
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro pasting (keyword)", "[preprocessor]") {
    auto& text = "`define FOO(x) x``gic\n`FOO(lo)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::LogicKeyword);
    CHECK(token.valueText() == "logic");
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro pasting (mixed)", "[preprocessor]") {
    auto& text = "`define FOO(x) ;``x\n`FOO(y)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::Semicolon);
    CHECK(token.valueText() == ";");
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro pasting (whitespace)", "[preprocessor]") {
    auto& text = "`define FOO(x) x`` y\n`FOO(a)";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "a");
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro stringify", "[preprocessor]") {
    auto& text = "`define FOO(x) `\" `\\`\" x``foo``42 `\\`\" `\"\n`FOO(bar_)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == " \" bar_foo42 \"");
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro stringify whitespace", "[preprocessor]") {
    auto& text = "`define FOO(x,y) `\" x ( y)\t  x   x`\"\n`FOO(bar,)";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == " bar ( )\t  bar   bar");
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro deferred define", "[preprocessor]") {
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

    logDiagnostics();

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(std::get<SVInt>(token.numericValue()) == 1);
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro string expansions", "[preprocessor]") {
    // These examples were all pulled from the spec.
    auto& text = R"(
`define D(x,y) initial $display("start", x , y, "end");

`D( "msg1" , "msg2" )
`D( " msg1", )
`D(, "msg2 ")
`D(,)
`D(  ,  )
`D("msg1")  // not enough args
`D()        // not enough args
`D(,,)      // too many args
`define MACRO1(a=5,b="B",c) $display(a,,b,,c);


`MACRO1 ( , 2, 3 )
`MACRO1 ( 1 , , 3 )
`MACRO1 ( , 2, )
`MACRO1 ( 1 ) // no default for C
`define MACRO2(a=5, b, c="C") $display(a,,b,,c);


`MACRO2 (1, , 3)
`MACRO2 (, 2, )
`MACRO2 (, 2)
`define MACRO3(a=5, b=0, c="C") $display(a,,b,,c);


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
    REQUIRE(diagnostics.count() == 5);
    CHECK(diagnostics[0].code == DiagCode::NotEnoughMacroArgs);
    CHECK(diagnostics[1].code == DiagCode::NotEnoughMacroArgs);
    CHECK(diagnostics[2].code == DiagCode::TooManyActualMacroArgs);
    CHECK(diagnostics[3].code == DiagCode::NotEnoughMacroArgs);
    CHECK(diagnostics[4].code == DiagCode::ExpectedMacroArgs);
}

TEST_CASE("IfDef branch (taken)", "[preprocessor]") {
    auto& text = "`define FOO\n`ifdef FOO\n42\n`endif";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(std::get<SVInt>(token.numericValue()) == 42);
    CHECK(diagnostics.empty());
}

TEST_CASE("IfDef branch (not taken)", "[preprocessor]") {
    auto& text = "`define FOO\n`ifdef BAR\n42\n`endif";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(diagnostics.empty());
}

TEST_CASE("IfNDef branch", "[preprocessor]") {
    auto& text = "`ifndef BAR\n42\n`endif";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(std::get<SVInt>(token.numericValue()) == 42);
    CHECK(diagnostics.empty());
}

TEST_CASE("ElseIf branch", "[preprocessor]") {
    auto& text = "`define FOO\n`ifdef BAR\n42\n`elsif FOO\n99`else\n1000`endif";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(std::get<SVInt>(token.numericValue()) == 99);
    CHECK(diagnostics.empty());
}

TEST_CASE("EndIf not done", "[preprocessor]") {
    auto& text = "`ifdef FOO\n`ifdef BAR\n42\n`endif\n1000\n`endif\n42.3";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::RealLiteral);
    CHECK(std::get<double>(token.numericValue()) == 42.3);
    CHECK(diagnostics.empty());
}

TEST_CASE("Nested branches", "[preprocessor]") {
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
    CHECK(std::get<SVInt>(token.numericValue()) == 99);
    CHECK(diagnostics.empty());
}

TEST_CASE("IfDef inside macro", "[preprocessor]") {
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
    CHECK(std::get<SVInt>(token.numericValue()) == 32);
    CHECK(diagnostics.empty());
}

TEST_CASE("LINE Directive", "[preprocessor]") {
    auto& text = "`__LINE__";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(std::get<SVInt>(token.numericValue()) == 1);
    CHECK(diagnostics.empty());
}

TEST_CASE("LINE Directive (include+nesting)", "[preprocessor]") {
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
    CHECK(std::get<SVInt>(token.numericValue()) == 5);
    CHECK(diagnostics.empty());
}

TEST_CASE("FILE Directive", "[preprocessor]") {
    auto& text = "`__FILE__";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::StringLiteral);
    // we set the name by default for files created this way as
    // <unnamed_bufferN> for some N, let's not be sensitive to that number
    CHECK(token.valueText().subString(0,15) == "<unnamed_buffer");
    CHECK(diagnostics.empty());
}

TEST_CASE("FILE Directive (include+nesting)", "[preprocessor]") {
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

    REQUIRE(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "file_uses_defn.svh");

    token = preprocessor.next();
    REQUIRE(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() != "file_uses_defn.svh");

    CHECK(diagnostics.empty());
}

TEST_CASE("undef Directive", "[preprocessor]") {
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

TEST_CASE("undef Directive 2", "[preprocessor]") {
    auto& text =
"`define FOO 45\n"
"`FOO\n"
"`undef FOO\n";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(std::get<SVInt>(token.numericValue()) == 45);
    CHECK(diagnostics.empty());
}

TEST_CASE("undefineall", "[preprocessor]") {
    auto& text =
"`define FOO 45\n"
"`undefineall\n"
"`FOO";
    Token token = lexToken(text);

    REQUIRE(token.kind == TokenKind::EndOfFile);
    CHECK(!diagnostics.empty());
}

TEST_CASE("begin_keywords", "[preprocessor]") {
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

    CHECK(diagnostics.empty());
}

TEST_CASE("begin_keywords (nested)", "[preprocessor]") {
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

    CHECK(diagnostics.empty());
}

TEST_CASE("timescale directive", "[preprocessor]") {
    lexToken("`timescale 10 ns / 1 fs");
    CHECK(diagnostics.empty());

    lexToken("`timescale 100 s / 10fs");
    CHECK(diagnostics.empty());

    lexToken("`timescale 1s/1fs");
    CHECK(diagnostics.empty());

    lexToken("`timescale 10fs / 100fs");
    CHECK(!diagnostics.empty());

    lexToken("`timescale 10fs 100ns");
    CHECK(!diagnostics.empty());

    lexToken("`timescale 1fs / 10us");
    CHECK(!diagnostics.empty());

    lexToken("`timescale 1 bs / 2fs");
    CHECK(!diagnostics.empty());

    lexToken("`timescale 1.2fs / 1fs");
    CHECK(!diagnostics.empty());
}

TEST_CASE("macro-defined include file", "[preprocessor]") {
    auto& text =
"`define FILE <include.svh>\n"
"`include `FILE";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "test string");
    CHECK(diagnostics.empty());

    auto& text2 =
"`define FILE \"include.svh\"\n"
"`include `FILE";
    token = lexToken(text2);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "test string");
    CHECK(diagnostics.empty());

    auto& text3 =
"`define FILE(arg) `\"arg`\"\n"
"`include `FILE(include.svh)";
    token = lexToken(text3);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "test string");
    CHECK(diagnostics.empty());


    auto& text4 =
"`define FILE <includesh\n"
"`include `FILE";
    token = lexToken(text4);

    CHECK(!diagnostics.empty());
}

}
