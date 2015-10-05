#include "catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

BumpAllocator alloc;
Diagnostics diagnostics;
SourceTracker sourceTracker;
Preprocessor preprocessor(sourceTracker, alloc, diagnostics);

ExpressionSyntax* parse(const SourceText& text) {
    diagnostics.clear();
    Lexer lexer(FileID(), text, preprocessor);
    Parser parser(lexer);

    auto node = parser.parseExpression();
    REQUIRE(node);
    return node;
}

TEST_CASE("Empty string", "[parser:expressions]") {
    auto& text = "";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::IdentifierName);
    // TODO:
    //CHECK(((IdentifierNameSyntax*)expr)->identifier.isMissing);
}

TEST_CASE("Name expression", "[parser:expressions]") {
    auto& text = "foo";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::IdentifierName);
    // TODO:
    //CHECK(((IdentifierNameSyntax*)expr)->identifier.isMissing);
    CHECK(expr->toString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Parenthesized expression", "[parser:expressions]") {
    auto& text = "(foo)";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::ParenthesizedExpression);
    CHECK(expr->toString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("MinTypMax expression", "[parser:expressions]") {
    auto& text = "(foo:34+99:baz)";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::ParenthesizedExpression);
    CHECK(((ParenthesizedExpressionSyntax*)expr)->expression->kind == SyntaxKind::MinTypMaxExpression);
    CHECK(expr->toString() == text);
    CHECK(diagnostics.empty());
}

void testImplicitClassHandle(TokenKind kind) {
    auto text = getTokenKindText(kind);
    auto expr = parse(SourceText::fromNullTerminated(text));

    REQUIRE(expr->kind == getKeywordNameExpression(kind));
    CHECK(((KeywordNameSyntax*)expr)->keyword->kind == kind);
    CHECK(diagnostics.empty());
}

TEST_CASE("Implicit class handles", "[parser:expressions]") {
    testImplicitClassHandle(TokenKind::ThisKeyword);
    testImplicitClassHandle(TokenKind::SuperKeyword);
}

TEST_CASE("String literal expression", "[parser:expressions]") {
    auto& text = "\"asdf\"";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::StringLiteralExpression);
    CHECK(expr->toString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Integer literal expression", "[parser:expressions]") {
    auto& text = "34'd56";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::IntegerLiteralExpression);
    CHECK(expr->toString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Real literal expression", "[parser:expressions]") {
    auto& text = "42.42";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::RealLiteralExpression);
    CHECK(expr->toString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Time literal expression", "[parser:expressions]") {
    auto& text = "42 ns";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::TimeLiteralExpression);
    CHECK(expr->toString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Null literal expression", "[parser:expressions]") {
    auto& text = "null";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::NullLiteralExpression);
    CHECK(expr->toString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Wildcard expression", "[parser:expressions]") {
    auto& text = "$";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::WildcardLiteralExpression);
    CHECK(expr->toString() == text);
    CHECK(diagnostics.empty());
}

void testPrefixUnary(TokenKind kind) {
    auto text = getTokenKindText(kind).toString() + "a";
    auto expr = parse(text);

    REQUIRE(expr->kind == getUnaryExpression(kind));
    CHECK(expr->toString() == text);
    CHECK(diagnostics.empty());
    auto us = (PrefixUnaryExpressionSyntax*)expr;
    CHECK(us->operatorToken->kind == kind);
    CHECK(us->operand->kind == SyntaxKind::IdentifierName);
}

TEST_CASE("Unary operators", "[parser:expressions]") {
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
}

void testHierarchicalName(const SourceText& text) {
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::HierarchicalName);
    CHECK(expr->toString() == text.begin());
    CHECK(diagnostics.empty());
}

TEST_CASE("Hierarchical identifiers", "[parser:expressions]") {
    testHierarchicalName("$root.foo.bar");
    testHierarchicalName("foo.bar");
    testHierarchicalName("$unit::foo.bar");
    testHierarchicalName("blah::foo.bar");
    testHierarchicalName("local::foo.bar");
}

TEST_CASE("Class scoped name", "[parser:expressions]") {
    // TODO
}

TEST_CASE("Empty queue", "[parser:expressions]") {
    auto& text = "{}";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::EmptyQueueExpression);
    CHECK(expr->toString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Concatenation", "[parser:expressions]") {
    auto& text = "{3+4, foo.bar}";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::ConcatenationExpression);
    CHECK(expr->toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Multiple concatenation", "[parser:expressions]") {
    auto& text = "{3+4 {foo.bar, 9**22}}";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::MultipleConcatenationExpression);
    CHECK(expr->toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Streaming concatenation", "[parser:expressions]") {
    auto& text = "{<< 3+9 {foo, 24.32}}";
    auto expr = parse(text);

    REQUIRE(expr->kind == SyntaxKind::StreamingConcatenationExpression);
    CHECK(expr->toFullString() == text);
    CHECK(diagnostics.empty());
}

// TODO: make this not stack overflow
//TEST_CASE("Big expression", "[parser:expressions]") {
//    auto& text =
//        "(stackDepth == 100) || ((stackDepth == 200) || ((stackDepth == 300) || ((stackDepth == 400) || ((stackDepth == 501) || ((stackDepth == 502) || ((stackDepth == 600) || ((stackDepth == 701) || ((stackDepth == 702) || ((stackDepth == 801) || ((stackDepth == 802) || ((stackDepth == 901) || ((stackDepth == 902) || ((stackDepth == 903) || ((stackDepth == 1001) || ((stackDepth == 1002) || ((stackDepth == 1101) || ((stackDepth == 1102) || ((stackDepth == 1201) || ((stackDepth == 1202) || ((stackDepth == 1301) || ((stackDepth == 1302) || ((stackDepth == 1401) || ((stackDepth == 1402) || ((stackDepth == 1403) || ((stackDepth == 1404) || ((stackDepth == 1405) || ((stackDepth == 1406) || ((stackDepth == 1407) || ((stackDepth == 1408) || ((stackDepth == 1409) || ((stackDepth == 1410) || ((stackDepth == 1411) || ((stackDepth == 1412) || ((stackDepth == 1413) || ((stackDepth == 1500) || ((stackDepth == 1601) || ((stackDepth == 1602) || ((stackDepth == 1701) || ((stackDepth == 1702) || ((stackDepth == 1703) || ((stackDepth == 1800) || ((stackDepth == 1901) || ((stackDepth == 1902) || ((stackDepth == 1903) || ((stackDepth == 1904) || ((stackDepth == 2000) || ((stackDepth == 2101) || ((stackDepth == 2102) || ((stackDepth == 2103) || ((stackDepth == 2104) || ((stackDepth == 2105) || ((stackDepth == 2106) || ((stackDepth == 2107) || ((stackDepth == 2201) || ((stackDepth == 2202) || ((stackDepth == 2203) || ((stackDepth == 2301) || ((stackDepth == 2302) || ((stackDepth == 2303) || ((stackDepth == 2304) || ((stackDepth == 2305) || ((stackDepth == 2401) || ((stackDepth == 2402) || ((stackDepth == 2403) || ((stackDepth == 2404) || ((stackDepth == 2501) || ((stackDepth == 2502) || ((stackDepth == 2503) || ((stackDepth == 2504) || ((stackDepth == 2505) || ((stackDepth == 2601) || ((stackDepth == 2602) || ((stackDepth == 2603) || ((stackDepth == 2604) || ((stackDepth == 2605) || ((stackDepth == 2606) || ((stackDepth == 2607) || ((stackDepth == 2608) || ((stackDepth == 2701) || ((stackDepth == 2702) || ((stackDepth == 2703) || ((stackDepth == 2704) || ((stackDepth == 2705) || ((stackDepth == 2706) || ((stackDepth == 2801) || ((stackDepth == 2802) || ((stackDepth == 2803) || ((stackDepth == 2804) || ((stackDepth == 2805) || ((stackDepth == 2806) || ((stackDepth == 2807) || ((stackDepth == 2808) || ((stackDepth == 2809) || ((stackDepth == 2810) || ((stackDepth == 2901) || ((stackDepth == 2902) || ((stackDepth == 3001) || ((stackDepth == 3002) || ((stackDepth == 3101) || ((stackDepth == 3102) || ((stackDepth == 3103) || ((stackDepth == 3104) || ((stackDepth == 3105) || ((stackDepth == 3201) || ((stackDepth == 3202) || ((stackDepth == 3203) || ((stackDepth == 3301) || ((stackDepth == 3302) || ((stackDepth == 3401) || ((stackDepth == 3402) || ((stackDepth == 3403) || ((stackDepth == 3404) || ((stackDepth == 3405) || ((stackDepth == 3406) || ((stackDepth == 3407) || ((stackDepth == 3408) || ((stackDepth == 3409) || ((stackDepth == 3410) || ((stackDepth == 3501) || ((stackDepth == 3502) || ((stackDepth == 3503) || ((stackDepth == 3504) || ((stackDepth == 3505) || ((stackDepth == 3506) || ((stackDepth == 3507) || ((stackDepth == 3508) || ((stackDepth == 3509) || ((stackDepth == 3601) || ((stackDepth == 3602) || ((stackDepth == 3701) || ((stackDepth == 3702) || ((stackDepth == 3703) || ((stackDepth == 3704) || ((stackDepth == 3705) || ((stackDepth == 3706) || ((stackDepth == 3801) || ((stackDepth == 3802) || ((stackDepth == 3803) || ((stackDepth == 3804) || ((stackDepth == 3805) || ((stackDepth == 3901) || ((stackDepth == 3902) || ((stackDepth == 3903) || ((stackDepth == 3904) || ((stackDepth == 3905) || ((stackDepth == 4001) || ((stackDepth == 4002) || ((stackDepth == 4003) || ((stackDepth == 4004) || ((stackDepth == 4005) || ((stackDepth == 4006) || ((stackDepth == 4007) || ((stackDepth == 4100) || ((stackDepth == 4201) || ((stackDepth == 4202) || ((stackDepth == 4203) || ((stackDepth == 4204) || ((stackDepth == 4301) || ((stackDepth == 4302) || ((stackDepth == 4304) || ((stackDepth == 4401) || ((stackDepth == 4402) || ((stackDepth == 4403) || ((stackDepth == 4404) || ((stackDepth == 4501) || ((stackDepth == 4502) || ((stackDepth == 4503) || ((stackDepth == 4504) || ((stackDepth == 4600) || ((stackDepth == 4701) || ((stackDepth == 4702) || ((stackDepth == 4801) || ((stackDepth == 4802) || ((stackDepth == 4803) || ((stackDepth == 4804) || ((stackDepth == 4805) || ((stackDepth == 4806) || ((stackDepth == 4807) || ((stackDepth == 4808) || ((stackDepth == 4809) || ((stackDepth == 4811) || ((stackDepth == 4901) || ((stackDepth == 4902) || ((stackDepth == 4903) || ((stackDepth == 4904) || ((stackDepth == 4905) || ((stackDepth == 4906) || ((stackDepth == 4907) || ((stackDepth == 4908) || ((stackDepth == 4909) || ((stackDepth == 4910) || ((stackDepth == 4911) || ((stackDepth == 4912) || ((stackDepth == 4913) || ((stackDepth == 4914) || ((stackDepth == 4915) || ((stackDepth == 4916) || ((stackDepth == 4917) || ((stackDepth == 4918) || ((stackDepth == 4919) || ((stackDepth == 4920) || ((stackDepth == 4921) || ((stackDepth == 4922) || ((stackDepth == 4923) || ((stackDepth == 5001) || ((stackDepth == 5002) || ((stackDepth == 5003) || ((stackDepth == 5004) || ((stackDepth == 5005) || ((stackDepth == 5006) || ((stackDepth == 5100) || ((stackDepth == 5200) || ((stackDepth == 5301) || ((stackDepth == 5302) || ((stackDepth == 5400) || ((stackDepth == 5500) || ((stackDepth == 5600) || ((stackDepth == 5700) || ((stackDepth == 5801) || ((stackDepth == 5802) || ((stackDepth == 5901) || ((stackDepth == 5902) || ((stackDepth == 6001) || ((stackDepth == 6002) || ((stackDepth == 6101) || ((stackDepth == 6102) || ((stackDepth == 6201) || ((stackDepth == 6202) || ((stackDepth == 6203) || ((stackDepth == 6204) || ((stackDepth == 6205) || ((stackDepth == 6301) || ((stackDepth == 6302) || ((stackDepth == 6401) || ((stackDepth == 6402) || ((stackDepth == 6501) || ((stackDepth == 6502) || ((stackDepth == 6503) || ((stackDepth == 6504) || ((stackDepth == 6601) || ((stackDepth == 6602) || ((stackDepth == 6701) || ((stackDepth == 6702) || ((stackDepth == 6703) || ((stackDepth == 6704) || ((stackDepth == 6801) || ((stackDepth == 6802) || ((stackDepth == 6901) || ((stackDepth == 6902) || ((stackDepth == 6903) || ((stackDepth == 6904) || ((stackDepth == 7001) || ((stackDepth == 7002) || ((stackDepth == 7101) || ((stackDepth == 7102) || ((stackDepth == 7103) || ((stackDepth == 7200) || ((stackDepth == 7301) || ((stackDepth == 7302) || ((stackDepth == 7400) || ((stackDepth == 7501) || ((stackDepth == 7502) || ((stackDepth == 7503) || ((stackDepth == 7600) || ((stackDepth == 7700) || ((stackDepth == 7800) || ((stackDepth == 7900) || ((stackDepth == 8001) || ((stackDepth == 8002) || ((stackDepth == 8101) || ((stackDepth == 8102) || ((stackDepth == 8103) || ((stackDepth == 8200) || ((stackDepth == 8300) || ((stackDepth == 8400) || ((stackDepth == 8501) || ((stackDepth == 8502) || ((stackDepth == 8601) || ((stackDepth == 8602) || ((stackDepth == 8700) || ((stackDepth == 8801) || ((stackDepth == 8802) || ((stackDepth == 8901) || ((stackDepth == 8902) || ((stackDepth == 8903) || ((stackDepth == 9001) || ((stackDepth == 9002) || ((stackDepth == 9003) || ((stackDepth == 9004) || ((stackDepth == 9005) || ((stackDepth == 9101) || ((stackDepth == 9102) || ((stackDepth == 9200) || ((stackDepth == 9300) || ((stackDepth == 9401) || ((stackDepth == 9402) || ((stackDepth == 9403) || ((stackDepth == 9500) || ((stackDepth == 9601) || ((stackDepth == 9602) || ((stackDepth == 9701) || ((stackDepth == 9702) || ((stackDepth == 9801) || ((stackDepth == 9802) || ((stackDepth == 9900) || ((stackDepth == 10000) || ((stackDepth == 10100) || ((stackDepth == 10201) || ((stackDepth == 10202) || ((stackDepth == 10301) || ((stackDepth == 10302) || ((stackDepth == 10401) || ((stackDepth == 10402) || ((stackDepth == 10403) || ((stackDepth == 10501) || ((stackDepth == 10502) || ((stackDepth == 10601) || ((stackDepth == 10602) || ((stackDepth == 10701) || ((stackDepth == 10702) || ((stackDepth == 10703) || ((stackDepth == 10704) || ((stackDepth == 10705) || ((stackDepth == 10706) || ((stackDepth == 10801) || ((stackDepth == 10802) || ((stackDepth == 10803) || ((stackDepth == 10804) || ((stackDepth == 10805) || ((stackDepth == 10806) || ((stackDepth == 10807) || ((stackDepth == 10808) || ((stackDepth == 10809) || ((stackDepth == 10900) || ((stackDepth == 11000) || ((stackDepth == 11100) || ((stackDepth == 11201) || ((stackDepth == 11202) || ((stackDepth == 11203) || ((stackDepth == 11204) || ((stackDepth == 11205) || ((stackDepth == 11206) || ((stackDepth == 11207) || ((stackDepth == 11208) || ((stackDepth == 11209) || ((stackDepth == 11210) || ((stackDepth == 11211) || ((stackDepth == 11212) || ((stackDepth == 11213) || ((stackDepth == 11214) || ((stackDepth == 11301) || ((stackDepth == 11302) || ((stackDepth == 11303) || ((stackDepth == 11304) || ((stackDepth == 11305) || ((stackDepth == 11306) || ((stackDepth == 11307) || ((stackDepth == 11308) || ((stackDepth == 11309) || ((stackDepth == 11401) || ((stackDepth == 11402) || ((stackDepth == 11403) || ((stackDepth == 11404) || ((stackDepth == 11501) || ((stackDepth == 11502) || ((stackDepth == 11503) || ((stackDepth == 11504) || ((stackDepth == 11505) || ((stackDepth == 11601) || ((stackDepth == 11602) || ((stackDepth == 11603) || ((stackDepth == 11604) || ((stackDepth == 11605) || ((stackDepth == 11606) || ((stackDepth == 11701) || ((stackDepth == 11702) || ((stackDepth == 11800) || ((stackDepth == 11901) || ((stackDepth == 11902) || ((stackDepth == 11903) || ((stackDepth == 11904) || ((stackDepth == 11905) || ((stackDepth == 12001) || ((stackDepth == 12002) || ((stackDepth == 12003) || ((stackDepth == 12004) || ((stackDepth == 12101) || ((stackDepth == 12102) || ((stackDepth == 12103) || ((stackDepth == 12104) || ((stackDepth == 12105) || ((stackDepth == 12106) || ((stackDepth == 12107) || ((stackDepth == 12108) || ((stackDepth == 12109) || ((stackDepth == 12110) || ((stackDepth == 12111) || ((stackDepth == 12112) || ((stackDepth == 12113) || ((stackDepth == 12114) || ((stackDepth == 12115) || ((stackDepth == 12116) || ((stackDepth == 12201) || ((stackDepth == 12202) || ((stackDepth == 12203) || ((stackDepth == 12204) || ((stackDepth == 12205) || ((stackDepth == 12301) || ((stackDepth == 12302) || ((stackDepth == 12401) || ((stackDepth == 12402) || ((stackDepth == 12403) || ((stackDepth == 12404) || ((stackDepth == 12405) || ((stackDepth == 12406) || ((stackDepth == 12501) || ((stackDepth == 12502) || ((stackDepth == 12601) || ((stackDepth == 12602) || ((stackDepth == 12603) || ((stackDepth == 12700) || ((stackDepth == 12800) || ((stackDepth == 12900) || ((stackDepth == 13001) || ((stackDepth == 13002) || ((stackDepth == 13003) || ((stackDepth == 13004) || ((stackDepth == 13005) || "
//        "((stackDepth == 13101) || ((stackDepth == 13102) || ((stackDepth == 13103) || ((stackDepth == 13201) || ((stackDepth == 13202) || ((stackDepth == 13203) || ((stackDepth == 13301) || ((stackDepth == 13302) || ((stackDepth == 13303) || ((stackDepth == 13304) || ((stackDepth == 13401) || ((stackDepth == 13402) || ((stackDepth == 13403) || ((stackDepth == 13404) || ((stackDepth == 13405) || ((stackDepth == 13501) || ((stackDepth == 13502) || ((stackDepth == 13600) || ((stackDepth == 13701) || ((stackDepth == 13702) || ((stackDepth == 13703) || ((stackDepth == 13800) || ((stackDepth == 13901) || ((stackDepth == 13902) || ((stackDepth == 13903) || ((stackDepth == 14001) || ((stackDepth == 14002) || ((stackDepth == 14100) || ((stackDepth == 14200) || ((stackDepth == 14301) || ((stackDepth == 14302) || ((stackDepth == 14400) || ((stackDepth == 14501) || ((stackDepth == 14502) || ((stackDepth == 14601) || ((stackDepth == 14602) || ((stackDepth == 14603) || ((stackDepth == 14604) || ((stackDepth == 14605) || ((stackDepth == 14606) || ((stackDepth == 14607) || ((stackDepth == 14701) || ((stackDepth == 14702) || ((stackDepth == 14703) || ((stackDepth == 14704) || ((stackDepth == 14705) || ((stackDepth == 14706) || ((stackDepth == 14707) || ((stackDepth == 14708) || ((stackDepth == 14709) || ((stackDepth == 14710) || ((stackDepth == 14711) || ((stackDepth == 14712) || ((stackDepth == 14713) || ((stackDepth == 14714) || ((stackDepth == 14715) || ((stackDepth == 14716) || ((stackDepth == 14717) || ((stackDepth == 14718) || ((stackDepth == 14719) || ((stackDepth == 14720 || ((stackDepth == 14717 || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717 || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717 || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717) || ((stackDepth == 14717))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));";
//    auto expr = parse(text);
//
//
//}

TEST_CASE("Arithmetic expressions", "[parser]") {
    auto expr = parse("3 + 4 / 2 * 9");
    REQUIRE(expr->kind == SyntaxKind::AddExpression);
    CHECK(((BinaryExpressionSyntax*)expr)->right->kind == SyntaxKind::MultiplyExpression);
}

}