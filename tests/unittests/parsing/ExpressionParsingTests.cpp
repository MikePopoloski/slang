// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/SyntaxPrinter.h"

using LF = LexerFacts;

TEST_CASE("Empty string") {
    auto& text = "";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::IdentifierName);
    CHECK(expr.as<IdentifierNameSyntax>().identifier.isMissing());
}

TEST_CASE("Name expression") {
    auto& text = "foo";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::IdentifierName);
    CHECK(!expr.as<IdentifierNameSyntax>().identifier.isMissing());
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Parenthesized expression") {
    auto& text = "(foo)";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::ParenthesizedExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("MinTypMax expression") {
    auto& text = "(foo:34+99:baz)";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::ParenthesizedExpression);
    CHECK(expr.as<ParenthesizedExpressionSyntax>().expression->kind ==
          SyntaxKind::MinTypMaxExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("String literal expression") {
    auto& text = "\"asdf\"";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::StringLiteralExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Integer literal expression") {
    auto& text = "34'd56";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::IntegerVectorExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Integer with question") {
    auto& text = "4'b?10?";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::IntegerVectorExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Real literal expression") {
    auto& text = "42.42";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::RealLiteralExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Time literal expression") {
    auto& text = "42ns";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::TimeLiteralExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Null literal expression") {
    auto& text = "null";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::NullLiteralExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Wildcard expression") {
    auto& text = "$";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::WildcardLiteralExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

void testPrefixUnary(TokenKind kind) {
    auto text = std::string(LF::getTokenKindText(kind)) + "a";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxFacts::getUnaryPrefixExpression(kind));
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
    auto& us = expr.as<PrefixUnaryExpressionSyntax>();
    CHECK(us.operatorToken.kind == kind);
    CHECK(us.operand->kind == SyntaxKind::IdentifierName);
}

TEST_CASE("Unary prefix operators") {
    testPrefixUnary(TokenKind::Plus);
    testPrefixUnary(TokenKind::Minus);
    testPrefixUnary(TokenKind::And);
    testPrefixUnary(TokenKind::TildeAnd);
    testPrefixUnary(TokenKind::Or);
    testPrefixUnary(TokenKind::TildeOr);
    testPrefixUnary(TokenKind::Xor);
    testPrefixUnary(TokenKind::XorTilde);
    testPrefixUnary(TokenKind::TildeXor);
    testPrefixUnary(TokenKind::DoublePlus);
    testPrefixUnary(TokenKind::DoubleMinus);
    testPrefixUnary(TokenKind::Tilde);
    testPrefixUnary(TokenKind::Exclamation);
}

void testPostfixUnary(TokenKind kind) {
    auto text = "a" + std::string(LF::getTokenKindText(kind));
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxFacts::getUnaryPostfixExpression(kind));
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
    auto& us = expr.as<PostfixUnaryExpressionSyntax>();
    CHECK(us.operatorToken.kind == kind);
    CHECK(us.operand->kind == SyntaxKind::IdentifierName);
}

TEST_CASE("Unary postfix operators") {
    testPostfixUnary(TokenKind::DoublePlus);
    testPostfixUnary(TokenKind::DoubleMinus);
}

void testBinaryOperator(TokenKind kind) {
    auto text = "a " + std::string(LF::getTokenKindText(kind)) + " 4";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxFacts::getBinaryExpression(kind));
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
    auto& us = expr.as<BinaryExpressionSyntax>();
    CHECK(us.operatorToken.kind == kind);
    CHECK(us.left->kind == SyntaxKind::IdentifierName);
    CHECK(us.right->kind == SyntaxKind::IntegerLiteralExpression);
}

TEST_CASE("Binary operators") {
    testBinaryOperator(TokenKind::Plus);
    testBinaryOperator(TokenKind::Minus);
    testBinaryOperator(TokenKind::Star);
    testBinaryOperator(TokenKind::Slash);
    testBinaryOperator(TokenKind::Percent);
    testBinaryOperator(TokenKind::DoubleStar);
    testBinaryOperator(TokenKind::DoubleEquals);
    testBinaryOperator(TokenKind::ExclamationEquals);
    testBinaryOperator(TokenKind::TripleEquals);
    testBinaryOperator(TokenKind::ExclamationDoubleEquals);
    testBinaryOperator(TokenKind::DoubleEqualsQuestion);
    testBinaryOperator(TokenKind::ExclamationEqualsQuestion);
    testBinaryOperator(TokenKind::DoubleAnd);
    testBinaryOperator(TokenKind::DoubleOr);
    testBinaryOperator(TokenKind::MinusArrow);
    testBinaryOperator(TokenKind::LessThanMinusArrow);
    testBinaryOperator(TokenKind::LessThan);
    testBinaryOperator(TokenKind::LessThanEquals);
    testBinaryOperator(TokenKind::GreaterThan);
    testBinaryOperator(TokenKind::GreaterThanEquals);
    testBinaryOperator(TokenKind::And);
    testBinaryOperator(TokenKind::Or);
    testBinaryOperator(TokenKind::Xor);
    testBinaryOperator(TokenKind::XorTilde);
    testBinaryOperator(TokenKind::TildeXor);
    testBinaryOperator(TokenKind::RightShift);
    testBinaryOperator(TokenKind::TripleRightShift);
    testBinaryOperator(TokenKind::LeftShift);
    testBinaryOperator(TokenKind::TripleLeftShift);
    testBinaryOperator(TokenKind::Equals);
    testBinaryOperator(TokenKind::PlusEqual);
    testBinaryOperator(TokenKind::MinusEqual);
    testBinaryOperator(TokenKind::StarEqual);
    testBinaryOperator(TokenKind::SlashEqual);
    testBinaryOperator(TokenKind::PercentEqual);
    testBinaryOperator(TokenKind::AndEqual);
    testBinaryOperator(TokenKind::OrEqual);
    testBinaryOperator(TokenKind::XorEqual);
    testBinaryOperator(TokenKind::LeftShiftEqual);
    testBinaryOperator(TokenKind::TripleLeftShiftEqual);
    testBinaryOperator(TokenKind::RightShiftEqual);
    testBinaryOperator(TokenKind::TripleRightShiftEqual);
}

void testScopedName(std::string_view text) {
    auto& expr = parseExpression(std::string(text));

    REQUIRE(expr.kind == SyntaxKind::ScopedName);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Scoped identifiers") {
    testScopedName("$unit::stuff");
    testScopedName("$root.asdf");
    testScopedName("foo::bar");
    testScopedName("$unit::foo::bar");
    testScopedName("blah::foo::bar");
    testScopedName("local::foo::bar");
}

TEST_CASE("Class scoped name") {
    auto& text = "blah::foo #(stuff, .thing(3+9))::bar";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::ScopedName);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Empty queue") {
    auto& text = "{}";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::EmptyQueueExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Concatenation") {
    auto& text = "{3+4, foo.bar}";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::ConcatenationExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Concatenation (single)") {
    auto& text = "{3+4}";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::ConcatenationExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Multiple concatenation") {
    auto& text = "{3+4 {foo.bar, 9**22}}";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::MultipleConcatenationExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Streaming concatenation") {
    auto& text = "{<< 3+9 {foo, 24.32 with [3+:4]}}";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::StreamingConcatenationExpression);
    CHECK(expr.as<StreamingConcatenationExpressionSyntax>()
              .expressions[1]
              ->withRange->range->selector->kind == SyntaxKind::AscendingRangeSelect);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Element Access") {
    auto& text = "(foo).bar[3][9+4]";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::ElementSelectExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

void testElementRange(std::string_view text, SyntaxKind kind) {
    auto& expr = parseExpression(std::string(text));
    REQUIRE(expr.kind == SyntaxKind::ElementSelectExpression);
    CHECK(expr.as<ElementSelectExpressionSyntax>().select->selector->kind == kind);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Element range") {
    testElementRange("(foo).bar[3:4]", SyntaxKind::SimpleRangeSelect);
    testElementRange("(foo).bar[3+:4]", SyntaxKind::AscendingRangeSelect);
    testElementRange("(foo).bar[3-:4]", SyntaxKind::DescendingRangeSelect);
}

TEST_CASE("Member Access") {
    auto& text = "(foo).bar";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::MemberAccessExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Invocation expression") {
    auto& text = "foo.bar(5, 6, .param(9))";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::InvocationExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Inside expression") {
    auto& text = "34 inside { 34, [12:12], 19 }";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::InsideExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Tagged union expression") {
    auto& text = "tagged foo";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::TaggedUnionExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Bad argument recovery") {
    auto& text = "foo(]], 3 4,)";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::InvocationExpression);
    CHECK(expr.toString() == "foo(");
    CHECK(!diagnostics.empty());
}

TEST_CASE("Conditional expression") {
    // check proper precedence
    auto& text = "foo || bar ? 3 : 4";
    auto& expr = parseExpression(text);

    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
    REQUIRE(expr.kind == SyntaxKind::ConditionalExpression);

    auto& cond = expr.as<ConditionalExpressionSyntax>();
    REQUIRE(cond.predicate->conditions.size() == 1);
    CHECK(cond.predicate->conditions[0]->expr->kind == SyntaxKind::LogicalOrExpression);
}

TEST_CASE("Conditional expression (pattern matching)") {
    // check proper precedence
    auto& text = "foo matches 34 &&& foo ? 3 : 4";
    auto& expr = parseExpression(text);

    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
    REQUIRE(expr.kind == SyntaxKind::ConditionalExpression);

    auto& cond = expr.as<ConditionalExpressionSyntax>();
    REQUIRE(cond.predicate->conditions.size() == 2);
    CHECK(cond.predicate->conditions[0]->expr->kind == SyntaxKind::IdentifierName);
    CHECK(cond.predicate->conditions[0]->matchesClause->pattern->kind ==
          SyntaxKind::ExpressionPattern);
}

#if __cpp_exceptions
TEST_CASE("Big expression") {
    auto& text = R"(
module M; localparam foo = (stackDepth == 100) || ((stackDepth == 200) || ((stackDepth ==
300) || ((stackDepth == 400) || ((stackDepth == 501) || ((stackDepth == 502) ||
((stackDepth == 600) ||
((stackDepth == 701) || ((stackDepth == 702) || ((stackDepth == 801) || ((stackDepth ==
802) || ((stackDepth == 901) || ((stackDepth == 902) || ((stackDepth == 903) ||
((stackDepth == 10201) || ((stackDepth == 10202) || ((stackDepth == 10301) ||
((stackDepth == 10302) || ((stackDepth == 10401) || ((stackDepth == 10402) ||
((stackDepth == 10403) || ((stackDepth == 10501) || ((stackDepth == 10502) ||
((stackDepth == 10601) || ((stackDepth == 10602) || ((stackDepth == 10701) ||
((stackDepth == 10702) || ((stackDepth == 10703) || ((stackDepth == 10704) ||
((stackDepth == 10705) || ((stackDepth == 10706) || ((stackDepth == 10801) ||
((stackDepth == 10802) || ((stackDepth == 10803) || ((stackDepth == 10804) ||
((stackDepth == 10805) || ((stackDepth == 10806) || ((stackDepth == 10807) ||
((stackDepth == 10808) || ((stackDepth == 10809) || ((stackDepth == 10900) ||
((stackDepth == 11000) || ((stackDepth == 11100) || ((stackDepth == 11201) ||
((stackDepth == 11202) || ((stackDepth == 11203) || ((stackDepth == 11204) ||
((stackDepth == 11205) || ((stackDepth == 11206) || ((stackDepth == 11207) ||
((stackDepth == 11208) || ((stackDepth == 11209) || ((stackDepth == 11210) ||
((stackDepth == 11211) || ((stackDepth == 11212) || ((stackDepth == 11213) ||
((stackDepth == 11214) || ((stackDepth == 11301) || ((stackDepth == 11302) ||
((stackDepth == 11303) || ((stackDepth == 11304) || ((stackDepth == 11305) ||
((stackDepth == 11306) || ((stackDepth == 11307) || ((stackDepth == 11308) ||
((stackDepth == 11309) || ((stackDepth == 11401) || ((stackDepth == 11402) ||
((stackDepth == 11403) || ((stackDepth == 11404) || ((stackDepth == 11501) ||
((stackDepth == 11502) || ((stackDepth == 11503) || ((stackDepth == 11504) ||
((stackDepth == 11505) || ((stackDepth == 11601) || ((stackDepth == 11602) ||
((stackDepth == 11603) || ((stackDepth == 11604) || ((stackDepth == 11605) ||
((stackDepth == 11606) || ((stackDepth == 11701) || ((stackDepth == 11702) ||
((stackDepth == 11800) || ((stackDepth == 11901) || ((stackDepth == 11902) ||
((stackDepth == 11903) || ((stackDepth == 11904) || ((stackDepth == 11905) ||
((stackDepth == 12001) || ((stackDepth == 12002) || ((stackDepth == 12003) ||
((stackDepth == 12004) || ((stackDepth == 12101) || ((stackDepth == 12102) ||
((stackDepth == 12103) || ((stackDepth == 12104) || ((stackDepth == 12105) ||
((stackDepth == 12106) || ((stackDepth == 12107) || ((stackDepth == 12108) ||
((stackDepth == 12109) || ((stackDepth == 12110) || ((stackDepth == 12111) ||
((stackDepth == 12112) || ((stackDepth == 12113) || ((stackDepth == 12114) ||
((stackDepth == 12115) || ((stackDepth == 12116) || ((stackDepth == 12201) ||
((stackDepth == 12202) || ((stackDepth == 12203) || ((stackDepth == 12204) ||
((stackDepth == 12205) || ((stackDepth == 12301) || ((stackDepth == 12302) ||
((stackDepth == 12401) || ((stackDepth == 12402) || ((stackDepth == 12403) ||
((stackDepth == 12404) || ((stackDepth == 12405) || ((stackDepth == 12406) ||
((stackDepth == 12501) || ((stackDepth == 12502) || ((stackDepth == 12601) ||
((stackDepth == 12602) || ((stackDepth == 12603) || ((stackDepth == 12700) ||
((stackDepth == 12800) || ((stackDepth == 12900) || ((stackDepth == 13001) ||
((stackDepth == 13002) || ((stackDepth == 13003) || ((stackDepth == 13004) ||
((stackDepth == 13005) ||
((stackDepth == 13101) || ((stackDepth == 13102) || ((stackDepth == 13103) ||
((stackDepth == 13201) || ((stackDepth == 13202) || ((stackDepth == 13203) ||
((stackDepth == 13301) || ((stackDepth == 13302) || ((stackDepth == 13303) ||
((stackDepth == 13304) || ((stackDepth == 13401) || ((stackDepth == 13402) ||
((stackDepth == 13403) || ((stackDepth == 13404) || ((stackDepth == 13405) ||
((stackDepth == 13501) || ((stackDepth == 13502) || ((stackDepth == 13600) ||
((stackDepth == 13701) || ((stackDepth == 13702) || ((stackDepth == 13703) ||
((stackDepth == 13800) || ((stackDepth == 13901) || ((stackDepth == 13902) ||
((stackDepth == 13903) || ((stackDepth == 14001) || ((stackDepth == 14002) ||
((stackDepth == 14100) || ((stackDepth == 14200) || ((stackDepth == 14301) ||
((stackDepth == 14302) || ((stackDepth == 14400) || ((stackDepth == 14501) ||
((stackDepth == 14502) || ((stackDepth == 14601) || ((stackDepth == 14602) ||
((stackDepth == 14603) || ((stackDepth == 14604) || ((stackDepth == 14605) ||
((stackDepth == 14606) || ((stackDepth == 14607) || ((stackDepth == 14701) ||
((stackDepth == 14702) || ((stackDepth == 14703) || ((stackDepth == 14704) ||
((stackDepth == 14705) || ((stackDepth == 14706) || ((stackDepth == 14707) ||
((stackDepth == 14708) || ((stackDepth == 14709) || ((stackDepth == 14710) ||
((stackDepth == 14711) || ((stackDepth == 14712) || ((stackDepth == 14713) ||
((stackDepth == 14714) || ((stackDepth == 14715) || ((stackDepth == 14716) ||
((stackDepth == 14717) || ((stackDepth == 14718) || ((stackDepth == 14719) ||
((stackDepth == 14720 || ((stackDepth == 14717 || ((stackDepth == 14717) || ((stackDepth
== 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717)
|| ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717 || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth
== 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717)
|| ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) ||
((stackDepth == 14717) || ((stackDepth == 14717 || ((stackDepth == 14717);
)";

    Diagnostics diags;
    Preprocessor preprocessor(SyntaxTree::getDefaultSourceManager(), alloc, diags);
    preprocessor.pushSource(text, "source");

    Bag options;
    ParserOptions parserOptions;
    parserOptions.maxRecursionDepth = 128;
    options.set(parserOptions);

    Parser parser(preprocessor, options);
    parser.parseCompilationUnit();

    std::string result = "\n" + report(diags);
    CHECK(result == R"(
source:23:43: error: language constructs are too deeply nested
((stackDepth == 11306) || ((stackDepth == 11307) || ((stackDepth == 11308) ||
                                          ^
)");
}
#endif

TEST_CASE("Arithmetic expressions") {
    auto& expr = parseExpression("3 + 4 / 2 * 9");
    REQUIRE(expr.kind == SyntaxKind::AddExpression);
    CHECK(expr.as<BinaryExpressionSyntax>().right->kind == SyntaxKind::MultiplyExpression);
}

TEST_CASE("Simple class new expression") {
    auto& text = "new";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::NewClassExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Scoped class new expression") {
    auto& text = "A::B#(3, \"foo\", bar[baz])::new";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::NewClassExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("New class with args") {
    auto& text = "A::B#(3, \"foo\", bar[baz])::new (a, , c)";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::NewClassExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Copy class expression") {
    auto& text = "new foo";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::CopyClassExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Scoped copy class expression -- error") {
    auto& text = "A::B::new foo";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::CopyClassExpression);
    CHECK(expr.toString() == text);
    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ScopedClassCopy);
}

TEST_CASE("New array expression parsing") {
    auto& text = "new [3]";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::NewArrayExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("New array expression with initializer") {
    auto& text = "new [3] (foo[bar])";
    auto& expr = parseExpression(text);

    REQUIRE(expr.kind == SyntaxKind::NewArrayExpression);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Error at EOF") {
    auto& text = "'d\n";
    parseExpression(text);

    std::string result = "\n" + reportGlobalDiags();
    CHECK(result == R"(
source:1:3: error: expected vector literal digits
'd
  ^
)");
}

TEST_CASE("scanTypePart test") {
    auto& text = "int i = a[d";
    parseCompilationUnit(text);
}

TEST_CASE("List parsing recovery") {
    auto& text = "assign foo = if";
    parseCompilationUnit(text);
}

void testExpr(std::string_view text, SyntaxKind kind) {
    auto& expr = parseExpression(std::string(text));

    REQUIRE(expr.kind == kind);
    CHECK(expr.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

void testMethodExpr(std::string_view text) {
    testExpr(text, SyntaxKind::ArrayOrRandomizeMethodExpression);
}

TEST_CASE("Array method expressions") {
    testExpr("asdf.foo (a, b)", SyntaxKind::InvocationExpression);
    testExpr("asdf.foo (* asdf *)", SyntaxKind::InvocationExpression);
    testExpr("asdf.foo (* asdf *) (a, b)", SyntaxKind::InvocationExpression);

    testMethodExpr("asdf.foo with (a > 0)");
    testMethodExpr("asdf.foo (a) with (a > 0)");
    testMethodExpr("asdf.foo (* asdf *) with (a > 0)");
    testMethodExpr("asdf.foo (* asdf *) (a) with (a > 0)");
}

TEST_CASE("Randomize method expressions") {
    testMethodExpr("asdf.randomize with {}");
    testMethodExpr("asdf.randomize with () {}");
    testMethodExpr("asdf.randomize with (a) {}");
    testMethodExpr("asdf.randomize with (a, b) {}");
}

void testConstraintBlock(std::string_view text) {
    testExpr("asdf.randomize with " + std::string(text),
             SyntaxKind::ArrayOrRandomizeMethodExpression);
}

TEST_CASE("Constraint block expressions") {
    testConstraintBlock("{atype == low;}");
    testConstraintBlock("{10 <= addr && addr <= 20;}");
    testConstraintBlock("{a inside {b, c};}");
    testConstraintBlock("{x != 200; x dist { [100:102] :/ 1, 200 := 2, 300 := 5};}");
    testConstraintBlock("{ unique {b, a[2:3], excluded}; }");
    testConstraintBlock("{ (a == 0) -> { b == 1; } }");
    testConstraintBlock("{ if (a == b) a < 10; else if (a == c) a > 100; }");
    testConstraintBlock("{ foreach (A[i]) A[i] inside {2,4,8,16}; }");
    testConstraintBlock("{ solve s before d; }");
    testConstraintBlock("{ soft mode -> length == 1024; }");
    testConstraintBlock("{ disable soft x; }");
}

TEST_CASE("Constraint block error recovery") {
    auto& text = "int i = foo.randomize with { end";
    parseCompilationUnit(text);
}

TEST_CASE("Assignment pattern error recovery") {
    auto& text = "int i = '{ asdf bazf gfdgh }";
    parseCompilationUnit(text);
}

TEST_CASE("Unary expression parsing error") {
    auto tree = SyntaxTree::fromText(R"(
module m;
  reg res;
  reg [1:0] in;
  initial begin
    res = ~ |in;
    res = ~ &in;
    res = ~ ^in;
  end
endmodule
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& diags = compilation.getAllDiagnostics();
    REQUIRE(diags.size() == 3);
    CHECK(diags[0].code == diag::ExpectedExpression);
    CHECK(diags[1].code == diag::ExpectedExpression);
    CHECK(diags[2].code == diag::ExpectedExpression);
}

TEST_CASE("Sequence expression parsing") {
    auto& text = R"(
module m;
  sequence s;
    ##[0:3]a ##1 (a ##1 b ##1 c) ##0 (d ##1 e ##1 f)
        ##1 (!frame && (data==data_bus)) || foo;
  endsequence
endmodule
)";
    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Property expression parsing") {
    auto& text = R"(
module m;
  property p1;
    @(posedge clk) a[*2] |-> ((##[1:3] c) or (d |=> e));
  endproperty

  property p2;
    a ##1 (b || c)[->1] |->
      if (b)
        (##1 d |-> e)
      else // c
        f ;
  endproperty

  property p3;
    (a + b) -> c;
  endproperty

  property p4;
    @(posedge clk) (valid, x = in) |-> ##4 (out == x + 4);
  endproperty
endmodule
)";
    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Invalid delay value expression parsing") {
    auto& text = R"(
module m;
    int i;
    initial begin
        #{1,2} i = 1;
        ##{1,2} i = 1;
    end
endmodule
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 2);
    CHECK(diagnostics[0].code == diag::InvalidDelayValue);
    CHECK(diagnostics[1].code == diag::InvalidDelayValue);
}

TEST_CASE("Pattern expression parsing") {
    auto& text = R"(
module m;
    initial begin
        case (instr) matches
            tagged Add '{.r1, .r2, .rd} &&& (rd != 0) : rf[rd] = rf[r1] + rf[r2];
            tagged Jmp .j : case (j) matches
                                tagged JmpU .a : pc = pc + a;
                                tagged JmpC '{.c, .a}: if (rf[c]) pc = a;
                            endcase
        endcase

        case (instr) matches
            tagged Add s: case (s) matches
                                '{.*, .*, 0} : ; // no op
                                '{.r1, .r2, .rd} : rf[rd] = rf[r1] + rf[r2];
                          endcase
            tagged Jmp .j: case (j) matches
                                tagged JmpU .a : pc = pc + a;
                                tagged JmpC '{.c, .a} : if (rf[c]) pc = a;
                           endcase
        endcase

        if (e matches (tagged Jmp (tagged JmpC '{cc:.c,addr:.a}))) begin
        end
    end
endmodule
)";
    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Dist expression parsing in disallowed contexts") {
    auto& text = R"(
class C;
    rand bit a;
    rand bit [3:0] b;
    constraint cmd_c {
        a  ->  b dist { 0 := 1, [1:15] := 1};
        a  -> (b dist { 0 := 1, [1:15] := 1});
    }

    int i = 1 + a dist {0 := 1, [1:15] := 1};
endclass
)";
    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 2);
    CHECK(diagnostics[0].code == diag::NonstandardDist);
    CHECK(diagnostics[1].code == diag::InvalidDistExpression);
}

TEST_CASE("Integer literal parsing regression GH #498") {
    auto& text = R"(
task foo(bit [31:0] a);
	$display("%x", a);
endtask: foo

task test();
	foo(32'h0e+32'h4000);
endtask: test

module m;
initial begin
	test();
end
endmodule
)";
    auto& syntax = parseCompilationUnit(text);
    auto result = SyntaxPrinter().setSquashNewlines(false).print(syntax).str();
    CHECK(result == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Invalid integer literal base regression") {
    auto& text = R"(
module m;
    int i = #'d3;
endmodule
)";
    auto& syntax = parseCompilationUnit(text);
    auto result = SyntaxPrinter().setSquashNewlines(false).print(syntax).str();
    CHECK(result == text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ExpectedIntegerLiteral);
}

TEST_CASE("Event control parsing regress GH #630") {
    auto& text = R"(
module t;
event e;
wire w;

// Named event, no parentheses, no delay, works
always @e
 begin
 end

// Named event, parentheses, delay, works
always @(e)
 #1
 begin
 end

// named event, no parenthesis, delay, doesn't work
always @e
 #1
 begin
 end

// wire, no parenthesis, delay, doesn't work
always @w
 #1
 begin
 end

endmodule
)";
    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Parsing select of a literal error") {
    auto tree = SyntaxTree::fromText(R"(
class C;
    rand int unsigned a;
    constraint test_c {
        a dist {
            1      :/ 9
            [2:10] :/ 1
        };
    }
endclass
)");

    Compilation compilation;
    compilation.addSyntaxTree(tree);

    auto& msg = compilation.getAllDiagnostics();
    std::string result = "\n" + report(msg);
    CHECK(result == R"(
source:6:24: error: expected ','
            1      :/ 9
                       ^
)");
}

TEST_CASE("Event control parsing @( *)") {
    auto& text = R"(
module t(a,b,ou);
	input a,b;
	output ou;
	reg a,b,ou;
	always @( *) begin
        ou <= a ^ b;
	end
endmodule
)";
    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Attributes disallowed on assignment operators") {
    auto& text = R"(
module m (input a, b, output c);
    assign c = (* foo *) a + (* foo *) b;
endmodule
)";
    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::AttributesNotAllowed);
}

TEST_CASE("Vector literal overflow parsing") {
    auto& text = R"(
shortint a = -16'sd32769;
int b = -32'sd2147483649;
int c = 32'd4294967297;

// No warnings for these
int d = 9'so777;
int e = 4'sb1000;
)";
    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 3);
    CHECK(diagnostics[0].code == diag::VectorLiteralOverflow);
    CHECK(diagnostics[1].code == diag::VectorLiteralOverflow);
    CHECK(diagnostics[2].code == diag::VectorLiteralOverflow);
}

TEST_CASE("Diagnosing missing base after signed specifier parsing") {
    auto& text = R"(
int i = 's3;
)";
    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ExpectedIntegerBaseAfterSigned);
}

TEST_CASE("Diagnosing real literal parsing errors") {
    auto& text = R"(
real r = 3.;
real s = 3._e+;
real s = 3e+_3;
)";
    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 4);
    CHECK(diagnostics[0].code == diag::MissingFractionalDigits);
    CHECK(diagnostics[1].code == diag::DigitsLeadingUnderscore);
    CHECK(diagnostics[2].code == diag::MissingExponentDigits);
    CHECK(diagnostics[3].code == diag::DigitsLeadingUnderscore);
}

TEST_CASE("Special case for literal overflow warning at int min") {
    auto& text = R"(
wire [15:0] x = -16'sd32768;
wire [15:0] x = -16'sh8000;
)";
    parseCompilationUnit(text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("v1800-2023: parsing default dist weight language version") {
    auto& text = R"(
class C;
    constraint c {
        a dist { default :/ 1 };
    }
endclass
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::WrongLanguageVersion);
}

TEST_CASE("Unbased unsized question mark parsing") {
    auto& text = R"(
module bug(input logic [1:0] a, input logic s, output logic [1:0]y);
    assign y = s? a: '?;
endmodule
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::ExpectedExpression);
}

TEST_CASE("Invalid select expression parsing") {
    auto& text = R"(
module signal_wrong (input logic [3:0] a,b, output logic [1:0] c);
    assign c = (a & b)[3:2];
endmodule
)";

    parseCompilationUnit(text);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::InvalidSelectExpression);
}
