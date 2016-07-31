#include "Catch/catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

BumpAllocator alloc;
Diagnostics diagnostics;

SourceManager& getSourceManager() {
    static SourceManager* sourceManager = nullptr;
    if (!sourceManager) {
        sourceManager = new SourceManager();
        sourceManager->addUserDirectory("../../../tests/unit_tests/data/");
    }
    return *sourceManager;
}

Token lexToken(StringRef text) {
    diagnostics.clear();

    Preprocessor preprocessor(getSourceManager(), alloc, diagnostics);
    preprocessor.pushSource(text);

    Token token = preprocessor.next();
    REQUIRE(token);
    return token;
}

TEST_CASE("Include File", "[preprocessor]") {
    auto& text = "`include \"include.svh\"";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == "test string");
    CHECK(diagnostics.empty());
}

void testDirective(SyntaxKind kind) {
    auto& text = getDirectiveText(kind);

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
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString(SyntaxToStringFlags::IncludeTrivia) == text);
    CHECK(diagnostics.empty());
    REQUIRE(token.trivia().count() == 1);
    REQUIRE(token.trivia()[0].kind == TriviaKind::Directive);

    auto def = token.trivia()[0].syntax()->as<DefineDirectiveSyntax>();
    CHECK(def->name.valueText() == "FOO");
    CHECK(def->endOfDirective);
    CHECK(def->directive);
    CHECK(!def->formalArguments);
    REQUIRE(def->body.count() == 3);
    CHECK(def->body[1].kind == TokenKind::IntegerLiteral);
}

TEST_CASE("Macro define (function-like)", "[preprocessor]") {
    auto& text = "`define FOO(a) a+1";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString(SyntaxToStringFlags::IncludeTrivia) == text);
    CHECK(diagnostics.empty());
    REQUIRE(token.trivia().count() == 1);
    REQUIRE(token.trivia()[0].kind == TriviaKind::Directive);

    auto def = token.trivia()[0].syntax()->as<DefineDirectiveSyntax>();
    CHECK(def->name.valueText() == "FOO");
    CHECK(def->endOfDirective);
    CHECK(def->directive);
    CHECK(def->formalArguments);
    CHECK(def->formalArguments->args.count() == 1);
    CHECK(def->formalArguments->args[0]->name.valueText() == "a");
    REQUIRE(def->body.count() == 3);
    CHECK(def->body[2].kind == TokenKind::IntegerLiteral);
}

TEST_CASE("Macro usage (undefined)", "[preprocessor]") {
    auto& text = "`FOO";
    auto& token = lexToken(text);

    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == DiagCode::UnknownDirective);
}

TEST_CASE("Macro usage (simple)", "[preprocessor]") {
    auto& text = "`define FOO 42\n`FOO";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.numericValue().integer == 42);
    CHECK(diagnostics.empty());
}

TEST_CASE("Function macro (simple)", "[preprocessor]") {
    auto& text = "`define FOO(x) x\n`FOO(3)";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.numericValue().integer == 3);
    CHECK(diagnostics.empty());
}

TEST_CASE("Function macro (defaults)", "[preprocessor]") {
    auto& text = "`define FOO(x=9(,), y=2) x\n`FOO()";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.numericValue().integer == 9);
    CHECK(diagnostics.empty());
}

TEST_CASE("Function macro (no tokens)", "[preprocessor]") {
    auto& text = "`define FOO(x=) x\n`FOO()";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::EndOfFile);
    CHECK(diagnostics.empty());
}

TEST_CASE("Function macro (simple nesting)", "[preprocessor]") {
    auto& text = "`define BLAHBLAH(x) x\n`define BAR(x) `BLAHBLAH(x)\n`define BAZ(x) `BAR(x)\n`define FOO(y) `BAZ(y)\n`FOO(15)";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.numericValue().integer == 15);
    CHECK(diagnostics.empty());
}

TEST_CASE("Function macro (arg nesting)", "[preprocessor]") {
    auto& text = "`define FOO(x) x\n`FOO(`FOO(3))";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.numericValue().integer == 3);
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro pasting (identifiers)", "[preprocessor]") {
    auto& text = "`define FOO(x,y) x   ``   _blah``y\n`FOO(   bar,    _BAZ)";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "bar_blah_BAZ");
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro pasting (operator)", "[preprocessor]") {
    auto& text = "`define FOO(x) x``+\n`FOO(+)";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::DoublePlus);
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro pasting (combination)", "[preprocessor]") {
    auto& text = "`define FOO(x,y) x``foo``y``42\n`FOO(bar_, 32)";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "bar_foo3242");
    CHECK(diagnostics.empty());
}

TEST_CASE("Macro stringify", "[preprocessor]") {
    auto& text = "`define FOO(x) `\" `\\`\" x``foo``42 `\\`\" `\"\n`FOO(bar_)";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::StringLiteral);
    CHECK(token.valueText() == " \" bar_foo42 \"");
    CHECK(diagnostics.empty());
}

TEST_CASE("IfDef branch (taken)", "[preprocessor]") {
    auto& text = "`define FOO\n`ifdef FOO\n42\n`endif";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.numericValue().integer == 42);
    CHECK(diagnostics.empty());
}

TEST_CASE("IfDef branch (not taken)", "[preprocessor]") {
    auto& text = "`define FOO\n`ifdef BAR\n42\n`endif";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(diagnostics.empty());
}

TEST_CASE("IfNDef branch", "[preprocessor]") {
    auto& text = "`ifndef BAR\n42\n`endif";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.numericValue().integer == 42);
    CHECK(diagnostics.empty());
}

TEST_CASE("ElseIf branch", "[preprocessor]") {
    auto& text = "`define FOO\n`ifdef BAR\n42\n`elsif FOO\n99`else\n1000`endif";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.numericValue().integer == 99);
    CHECK(diagnostics.empty());
}

TEST_CASE("EndIf not done", "[preprocessor]") {
    auto& text = "`ifdef FOO\n`ifdef BAR\n42\n`endif\n1000`endif\n42.3";
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::RealLiteral);
    CHECK(token.numericValue().real == 42.3);
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
    auto& token = lexToken(text);

    REQUIRE(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.numericValue().integer == 99);
    CHECK(diagnostics.empty());
}

}