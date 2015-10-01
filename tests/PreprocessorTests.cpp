#include "catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

BumpAllocator alloc;
Diagnostics diagnostics;

SourceTracker& getTracker() {
    static SourceTracker* tracker = nullptr;
    if (!tracker) {
        tracker = new SourceTracker();
        tracker->addUserDirectory("../../../tests/data/");
    }
    return *tracker;
}

const Token& lexToken(const SourceText& text) {
    diagnostics.clear();
    Preprocessor preprocessor(getTracker(), alloc, diagnostics);
    Lexer lexer(FileID(), text, preprocessor);

    Token* token = lexer.lex();
    REQUIRE(token != nullptr);
    return *token;
}

TEST_CASE("Include File", "[preprocessor]") {
    auto& text = "`include \"include.svh\"";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);

    // there should be one error about a non-existent include file
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::CouldNotOpenIncludeFile);
}

void testDirective(SyntaxKind kind) {
    auto& text = getDirectiveText(kind);

    diagnostics.clear();
    Preprocessor preprocessor(getTracker(), alloc, diagnostics);
    Lexer lexer(FileID(), SourceText::fromNullTerminated(text), preprocessor);

    Token* token = lexer.lexDirectiveMode();
    REQUIRE(token != nullptr);

    CHECK(token->kind == TokenKind::Directive);
    CHECK(token->toFullString() == text);
    CHECK(token->valueText() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Directives", "[preprocessor]") {
    testDirective(SyntaxKind::BeginKeywordsDirective);
    testDirective(SyntaxKind::CellDefineDirective);
    testDirective(SyntaxKind::DefaultNetTypeDirective);
    testDirective(SyntaxKind::DefineDirective);
    testDirective(SyntaxKind::ElseDirective);
    testDirective(SyntaxKind::ElseIfDirective);
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
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());
    REQUIRE(token.trivia.count() == 1);
    REQUIRE(token.trivia[0].kind == TriviaKind::Directive);

    auto def = token.trivia[0].syntax()->as<DefineDirectiveSyntax>();
    CHECK(def->name->valueText() == "FOO");
    CHECK(def->endOfDirective);
    CHECK(def->directive);
    CHECK(!def->formalArguments);
    REQUIRE(def->body.count() == 3);
    CHECK(def->body[1]->kind == TokenKind::IntegerLiteral);
}

TEST_CASE("Macro define (function-like)", "[preprocessor]") {
    auto& text = "`define FOO(a) a+1";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());
    REQUIRE(token.trivia.count() == 1);
    REQUIRE(token.trivia[0].kind == TriviaKind::Directive);

    auto def = token.trivia[0].syntax()->as<DefineDirectiveSyntax>();
    CHECK(def->name->valueText() == "FOO");
    CHECK(def->endOfDirective);
    CHECK(def->directive);
    CHECK(def->formalArguments);
    CHECK(def->formalArguments->args.count() == 1);
    CHECK(def->formalArguments->args[0]->name->valueText() == "a");
    REQUIRE(def->body.count() == 3);
    CHECK(def->body[2]->kind == TokenKind::IntegerLiteral);
}

TEST_CASE("Macro usage (undefined)", "[preprocessor]") {
    auto& text = "`FOO";
    auto& token = lexToken(text);

    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::UnknownDirective);
}

TEST_CASE("Macro usage (simple)", "[preprocessor]") {
    auto& text = "`define FOO 42\n`FOO";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.numericValue().integer == 42);
    CHECK(diagnostics.empty());
}

}