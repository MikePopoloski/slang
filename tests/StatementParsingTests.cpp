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

TEST_CASE("Case statement (normal)", "[parser:statements]") {
    auto& text = "unique case (foo) 3'd01: ; 3+9, foo: ; default; endcase";
    auto stmt = parse(text);

    REQUIRE(stmt->kind == SyntaxKind::CaseStatement);
    CHECK(stmt->toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Case statement (pattern)", "[parser:statements]") {
    auto& text = "priority casez (foo) matches .foo &&& bar: ; default; endcase";
    auto stmt = parse(text);

    REQUIRE(stmt->kind == SyntaxKind::CaseStatement);
    CHECK(stmt->toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Case statement (range)", "[parser:statements]") {
    auto& text = "casex (foo) inside 3, [4:2], [99]: ; default; endcase";
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

void testTimingControl(const SourceText& text, SyntaxKind kind) {
    auto stmt = parse(text);

    REQUIRE(stmt->kind == SyntaxKind::TimingControlStatement);
    CHECK(((TimingControlStatementSyntax*)stmt)->timingControl->kind == kind);
    CHECK(stmt->toFullString() == text.begin());
    CHECK(diagnostics.empty());
}

TEST_CASE("Timing control statements", "[parser:statements]") {
    testTimingControl("# 52 ;", SyntaxKind::DelayControl);
    testTimingControl("#1step ;", SyntaxKind::DelayControl);
    testTimingControl("# (3:4:5) ;", SyntaxKind::DelayControl);
    testTimingControl("## (3+2) ;", SyntaxKind::CycleDelay);
    testTimingControl("## foo ;", SyntaxKind::CycleDelay);
    testTimingControl("##92 ;", SyntaxKind::CycleDelay);
    testTimingControl("@* ;", SyntaxKind::ImplicitEventControl);
    testTimingControl("@ (*) ;", SyntaxKind::ParenImplicitEventControl);
    testTimingControl("@* ;", SyntaxKind::ImplicitEventControl);
    testTimingControl("@(posedge foo iff foo+92 == 76 or negedge clk, (edge clk)) ;", SyntaxKind::EventControlWithExpression);
}

}