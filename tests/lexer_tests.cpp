#include "catch.hpp"
#include "slang.h"

using namespace slang;

Allocator pool;
Diagnostics diagnostics;

bool withinUlp(double a, double b) {
    return std::abs(((int64_t)a - (int64_t)b)) <= 1;
}

const Token& LexToken(const std::string& text) {
    diagnostics.clear();
    Lexer lexer(text.c_str(), pool, diagnostics);

    Token* token = lexer.lex();
    REQUIRE(token != nullptr);
    return *token;
}

TEST_CASE("Line Comment", "[lexer]") {
    auto text = "// comment";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::LineComment);
    CHECK(diagnostics.empty());
}

TEST_CASE("Block Comment (one line)", "[lexer]") {
    auto text = "/* comment */";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::BlockComment);
    CHECK(diagnostics.empty());
}

TEST_CASE("Block Comment (multiple lines)", "[lexer]") {
    auto text =
R"(/*
comment on
multiple lines
*/)";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::BlockComment);
    CHECK(diagnostics.empty());
}

TEST_CASE("Whitespace", "[lexer]") {
    auto text = " \t\v\f token";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::Whitespace);
    CHECK(diagnostics.empty());
}

TEST_CASE("Newlines", "[lexer]") {
    auto text = "\r";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::EndOfLine);
    CHECK(diagnostics.empty());

    text = "\r\n";
    token = LexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::EndOfLine);
    CHECK(diagnostics.empty());

    text = "\n";
    token = LexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::EndOfLine);
    CHECK(diagnostics.empty());
}

TEST_CASE("Simple Identifiers", "[lexer]") {
    auto text = "a";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    text = "abc";
    token = LexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Mixed Identifiers", "[lexer]") {
    auto text = "a92837asdf358";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    text = "__a$$asdf213$";
    token = LexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Escaped Identifiers", "[lexer]") {
    auto text = "\\98\\#$%)(*lkjsd__09...asdf345";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("System Identifiers", "[lexer]") {
    auto text = "$hello";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::SystemIdentifier);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    text = "$45__hello";
    token = LexToken(text);
    CHECK(token.kind == TokenKind::SystemIdentifier);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal", "[lexer]") {
    auto text = "\"literal  #@$asdf\"";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal  #@$asdf");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (newline)", "[lexer]") {
    auto text = "\"literal\r\nwith new line\"";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() != text);
    CHECK(token.valueText() == "literal");

    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::NewlineInStringLiteral);
}

TEST_CASE("String literal (escaped newline)", "[lexer]") {
    auto text = "\"literal\\\r\nwith new line\"";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literalwith new line");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (unterminated)", "[lexer]") {
    auto text = "\"literal";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal");

    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::UnterminatedStringLiteral);
}

TEST_CASE("String literal (escapes)", "[lexer]") {
    auto text = "\"literal\\n\\t\\v\\f\\a \\\\ \\\" \"";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal\n\t\v\f\a \\ \" ");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (octal escape)", "[lexer]") {
    auto text = "\"literal\\377\"";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal\377");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (bad octal escape)", "[lexer]") {
    auto text = "\"literal\\400\"";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::OctalEscapeCodeTooBig);
}

TEST_CASE("String literal with hex escape", "[lexer]") {
    auto text = "\"literal\\xFa\"";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal\xFa");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (bad hex escape)", "[lexer]") {
    auto text = "\"literal\\xz\"";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literalz");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::InvalidHexEscapeCode);
}

TEST_CASE("String literal (unknown escape)", "[lexer]") {
    auto text = "\"literal\\i\"";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literali");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::UnknownEscapeCode);
}

TEST_CASE("Real literal (fraction)", "[lexer]") {
    auto text = "32.57";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(value.real == 32.57);
}

TEST_CASE("Real literal (missing fraction)", "[lexer]") {
    auto text = "32.";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::MissingFractionalDigits);

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(value.real == 32);
}

TEST_CASE("Real literal (exponent)", "[lexer]") {
    auto text = "32e57";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    double a = 32e57;
    CHECK(withinUlp(value.real, 32e57));
}

TEST_CASE("Real literal (plus exponent)", "[lexer]") {
    auto text = "32e+57";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(withinUlp(value.real, 32e+57));
}

TEST_CASE("Real literal (minus exponent)", "[lexer]") {
    auto text = "32e-57";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(withinUlp(value.real, 32e-57));
}

TEST_CASE("Real literal (fraction exponent)", "[lexer]") {
    auto text = "32.3456e57";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(value.real == 32.3456e57);
}

TEST_CASE("Real literal (exponent overflow)", "[lexer]") {
    auto text = "32e9000";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::RealExponentTooLarge);

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(std::isinf(value.real));
}

TEST_CASE("Real literal (digit overflow)", "[lexer]") {
    auto text = std::string(400, '9') + ".0";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::RealExponentTooLarge);

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(std::isinf(value.real));
}

void TestPunctuation(TokenKind kind) {
    auto text = GetTokenKindText(kind);
    auto token = LexToken(text);

    CHECK(token.kind == kind);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("All Punctuation", "[lexer]") {
    TestPunctuation(TokenKind::ApostropheOpenBrace);
    TestPunctuation(TokenKind::OpenBrace);
    TestPunctuation(TokenKind::CloseBrace);
    TestPunctuation(TokenKind::OpenBracket);
    TestPunctuation(TokenKind::CloseBracket);
    TestPunctuation(TokenKind::OpenParenthesis);
    TestPunctuation(TokenKind::OpenParenthesisStar);
    TestPunctuation(TokenKind::CloseParenthesis);
    TestPunctuation(TokenKind::StarCloseParenthesis);
    TestPunctuation(TokenKind::Semicolon);
    TestPunctuation(TokenKind::Colon);
    TestPunctuation(TokenKind::ColonEquals);
    TestPunctuation(TokenKind::ColonSlash);
    TestPunctuation(TokenKind::DoubleColon);
    TestPunctuation(TokenKind::StarDoubleColonStar);
    TestPunctuation(TokenKind::Comma);
    TestPunctuation(TokenKind::DotStar);
    TestPunctuation(TokenKind::Dot);
    TestPunctuation(TokenKind::Slash);
    TestPunctuation(TokenKind::Star);
    TestPunctuation(TokenKind::DoubleStar);
    TestPunctuation(TokenKind::StarArrow);
    TestPunctuation(TokenKind::Plus);
    TestPunctuation(TokenKind::DoublePlus);
    TestPunctuation(TokenKind::PlusColon);
    TestPunctuation(TokenKind::Minus);
    TestPunctuation(TokenKind::DoubleMinus);
    TestPunctuation(TokenKind::MinusColon);
    TestPunctuation(TokenKind::MinusArrow);
    TestPunctuation(TokenKind::MinusDoubleArrow);
    TestPunctuation(TokenKind::Tilde);
    TestPunctuation(TokenKind::TildeAnd);
    TestPunctuation(TokenKind::TildeOr);
    TestPunctuation(TokenKind::TildeXor);
    TestPunctuation(TokenKind::Dollar);
    TestPunctuation(TokenKind::Question);
    TestPunctuation(TokenKind::Hash);
    TestPunctuation(TokenKind::DoubleHash);
    TestPunctuation(TokenKind::HashMinusHash);
    TestPunctuation(TokenKind::HashEqualsHash);
    TestPunctuation(TokenKind::Xor);
    TestPunctuation(TokenKind::XorTilde);
    TestPunctuation(TokenKind::Equals);
    TestPunctuation(TokenKind::DoubleEquals);
    TestPunctuation(TokenKind::DoubleEqualsQuestion);
    TestPunctuation(TokenKind::TripleEquals);
    TestPunctuation(TokenKind::EqualsArrow);
    TestPunctuation(TokenKind::PlusEqual);
    TestPunctuation(TokenKind::MinusEqual);
    TestPunctuation(TokenKind::SlashEqual);
    TestPunctuation(TokenKind::StarEqual);
    TestPunctuation(TokenKind::AndEqual);
    TestPunctuation(TokenKind::OrEqual);
    TestPunctuation(TokenKind::PercentEqual);
    TestPunctuation(TokenKind::XorEqual);
    TestPunctuation(TokenKind::LeftShiftEqual);
    TestPunctuation(TokenKind::TripleLeftShiftEqual);
    TestPunctuation(TokenKind::RightShiftEqual);
    TestPunctuation(TokenKind::TripleRightShiftEqual);
    TestPunctuation(TokenKind::LeftShift);
    TestPunctuation(TokenKind::RightShift);
    TestPunctuation(TokenKind::TripleLeftShift);
    TestPunctuation(TokenKind::TripleRightShift);
    TestPunctuation(TokenKind::Exclamation);
    TestPunctuation(TokenKind::ExclamationEquals);
    TestPunctuation(TokenKind::ExclamationEqualsQuestion);
    TestPunctuation(TokenKind::ExclamationDoubleEquals);
    TestPunctuation(TokenKind::Percent);
    TestPunctuation(TokenKind::LessThan);
    TestPunctuation(TokenKind::LessThanEquals);
    TestPunctuation(TokenKind::LessThanMinusArrow);
    TestPunctuation(TokenKind::GreaterThan);
    TestPunctuation(TokenKind::GreaterThanEquals);
    TestPunctuation(TokenKind::Or);
    TestPunctuation(TokenKind::DoubleOr);
    TestPunctuation(TokenKind::OrMinusArrow);
    TestPunctuation(TokenKind::OrEqualsArrow);
    TestPunctuation(TokenKind::At);
    TestPunctuation(TokenKind::DoubleAt);
    TestPunctuation(TokenKind::And);
    TestPunctuation(TokenKind::DoubleAnd);
    TestPunctuation(TokenKind::TripleAnd);
}