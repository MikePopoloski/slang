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

void testDirective(TriviaKind kind) {
    auto& text = getTriviaKindText(kind);

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

TEST_CASE("Directives", "[lexer]") {
    testDirective(TriviaKind::BeginKeywordsDirective);
    testDirective(TriviaKind::CellDefineDirective);
    testDirective(TriviaKind::DefaultNetTypeDirective);
    testDirective(TriviaKind::DefineDirective);
    testDirective(TriviaKind::ElseDirective);
    testDirective(TriviaKind::ElseIfDirective);
    testDirective(TriviaKind::EndKeywordsDirective);
    testDirective(TriviaKind::EndCellDefineDirective);
    testDirective(TriviaKind::EndIfDirective);
    testDirective(TriviaKind::IfDefDirective);
    testDirective(TriviaKind::IfNDefDirective);
    testDirective(TriviaKind::IncludeDirective);
    testDirective(TriviaKind::LineDirective);
    testDirective(TriviaKind::NoUnconnectedDriveDirective);
    testDirective(TriviaKind::PragmaDirective);
    testDirective(TriviaKind::ResetAllDirective);
    testDirective(TriviaKind::TimescaleDirective);
    testDirective(TriviaKind::UnconnectedDriveDirective);
    testDirective(TriviaKind::UndefDirective);
    testDirective(TriviaKind::UndefineAllDirective);
}

//TEST_CASE("Macro usage", "[lexer]") {
//    auto& text = "`something";
//    auto& token = lexToken(text);
//
//    CHECK(token.kind == TokenKind::MacroUsage);
//    CHECK(token.toFullString() == text);
//    CHECK(token.valueText() == text);
//    CHECK(diagnostics.empty());
//}

}