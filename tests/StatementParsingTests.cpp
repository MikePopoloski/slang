#include "catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

BumpAllocator alloc;
Diagnostics diagnostics;
SourceTracker sourceTracker;
Preprocessor preprocessor(sourceTracker, alloc, diagnostics);

StatementSyntax* parse(const SourceText& text) {
    diagnostics.clear();
    Lexer lexer(FileID(), text, preprocessor);
    Parser parser(lexer);

    auto node = parser.parseStatement();
    REQUIRE(node);
    return node;
}

TEST_CASE("If statement", "[parser:statements]") {
    auto& text = "if (foo && bar &&& baz) ; else ;";
    auto stmt = parse(text);

    REQUIRE(stmt->kind == SyntaxKind::ConditionalStatement);
    CHECK(stmt->toFullString() == text);
    CHECK(diagnostics.empty());
    CHECK(((ConditionalStatementSyntax*)stmt)->predicate->conditions[0]->expr->kind == SyntaxKind::LogicalAndExpression);
}

TEST_CASE("Case statement (empty)", "[parser:statements]") {
    auto& text = "unique casez (foo) endcase";
    auto stmt = parse(text);

    REQUIRE(stmt->kind == SyntaxKind::CaseStatement);
    CHECK(stmt->toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Loop statements", "[parser:statements]") {
    auto& text = "while (foo) ;";
    auto stmt = parse(text);

    REQUIRE(stmt->kind == SyntaxKind::LoopStatement);
    CHECK(stmt->toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Do while statement", "[parser:statements]") {
    auto& text = "do ; while (foo) ;";
    auto stmt = parse(text);

    REQUIRE(stmt->kind == SyntaxKind::DoWhileStatement);
    CHECK(stmt->toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Forever statement", "[parser:statements]") {
    auto& text = "forever ;";
    auto stmt = parse(text);

    REQUIRE(stmt->kind == SyntaxKind::ForeverStatement);
    CHECK(stmt->toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Return statement", "[parser:statements]") {
    auto& text = "return foobar;";
    auto stmt = parse(text);

    REQUIRE(stmt->kind == SyntaxKind::ReturnStatement);
    CHECK(stmt->toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Jump statements", "[parser:statements]") {
    auto& text = "break;";
    auto stmt = parse(text);

    REQUIRE(stmt->kind == SyntaxKind::JumpStatement);
    CHECK(stmt->toFullString() == text);
    CHECK(diagnostics.empty());
}

}