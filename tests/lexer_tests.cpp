#include "catch.hpp"
#include "slang.h"

using namespace slang;

Allocator pool;
Diagnostics diagnostics;

bool withinUlp(double a, double b) {
    return std::abs(((int64_t)a - (int64_t)b)) <= 1;
}

const Token& lexToken(const std::string& text) {
    diagnostics.clear();
    Lexer lexer(text.c_str(), pool, diagnostics);

    Token* token = lexer.lex();
    REQUIRE(token != nullptr);
    return *token;
}

TEST_CASE("Line Comment", "[lexer]") {
    auto text = "// comment";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::LineComment);
    CHECK(diagnostics.empty());
}

TEST_CASE("Block Comment (one line)", "[lexer]") {
    auto text = "/* comment */";
    auto token = lexToken(text);

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
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::BlockComment);
    CHECK(diagnostics.empty());
}

TEST_CASE("Whitespace", "[lexer]") {
    auto text = " \t\v\f token";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::Whitespace);
    CHECK(diagnostics.empty());
}

TEST_CASE("Newlines", "[lexer]") {
    auto text = "\r";
    auto token = lexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::EndOfLine);
    CHECK(diagnostics.empty());

    text = "\r\n";
    token = lexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::EndOfLine);
    CHECK(diagnostics.empty());

    text = "\n";
    token = lexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::EndOfLine);
    CHECK(diagnostics.empty());
}

TEST_CASE("Simple Identifiers", "[lexer]") {
    auto text = "a";
    auto token = lexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == text);
    CHECK(token.identifierType() == IdentifierType::Normal);
    CHECK(diagnostics.empty());

    text = "abc";
    token = lexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == text);
    CHECK(token.identifierType() == IdentifierType::Normal);
    CHECK(diagnostics.empty());
}

TEST_CASE("Mixed Identifiers", "[lexer]") {
    auto text = "a92837asdf358";
    auto token = lexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == text);
    CHECK(token.identifierType() == IdentifierType::Normal);
    CHECK(diagnostics.empty());

    text = "__a$$asdf213$";
    token = lexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == text);
    CHECK(token.identifierType() == IdentifierType::Normal);
    CHECK(diagnostics.empty());
}

TEST_CASE("Escaped Identifiers", "[lexer]") {
    auto text = "\\98\\#$%)(*lkjsd__09...asdf345";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "98\\#$%)(*lkjsd__09...asdf345");
    CHECK(token.identifierType() == IdentifierType::Escaped);
    CHECK(diagnostics.empty());
}

TEST_CASE("System Identifiers", "[lexer]") {
    auto text = "$hello";
    auto token = lexToken(text);
    CHECK(token.kind == TokenKind::SystemIdentifier);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == text);
    CHECK(token.identifierType() == IdentifierType::System);
    CHECK(diagnostics.empty());

    text = "$45__hello";
    token = lexToken(text);
    CHECK(token.kind == TokenKind::SystemIdentifier);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == text);
    CHECK(token.identifierType() == IdentifierType::System);
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal", "[lexer]") {
    auto text = "\"literal  #@$asdf\"";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal  #@$asdf");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (newline)", "[lexer]") {
    auto text = "\"literal\r\nwith new line\"";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() != text);
    CHECK(token.valueText() == "literal");

    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::NewlineInStringLiteral);
}

TEST_CASE("String literal (escaped newline)", "[lexer]") {
    auto text = "\"literal\\\r\nwith new line\"";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literalwith new line");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (unterminated)", "[lexer]") {
    auto text = "\"literal";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal");

    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::UnterminatedStringLiteral);
}

TEST_CASE("String literal (escapes)", "[lexer]") {
    auto text = "\"literal\\n\\t\\v\\f\\a \\\\ \\\" \"";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal\n\t\v\f\a \\ \" ");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (octal escape)", "[lexer]") {
    auto text = "\"literal\\377\"";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal\377");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (bad octal escape)", "[lexer]") {
    auto text = "\"literal\\400\"";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::OctalEscapeCodeTooBig);
}

TEST_CASE("String literal with hex escape", "[lexer]") {
    auto text = "\"literal\\xFa\"";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal\xFa");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (bad hex escape)", "[lexer]") {
    auto text = "\"literal\\xz\"";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literalz");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::InvalidHexEscapeCode);
}

TEST_CASE("String literal (unknown escape)", "[lexer]") {
    auto text = "\"literal\\i\"";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literali");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::UnknownEscapeCode);
}

TEST_CASE("Signed integer literal", "[lexer]") {
    auto text = "19248";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::SignedInteger);
    CHECK(value.integer == 19248);
}

TEST_CASE("Signed integer literal (trailing whitespace)", "[lexer]") {
    // based numeric literals can have whitespace between them and the base,
    // token so the literal lexer needs to handle that speculatively
    auto text = "19248         \v\t ";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() != text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::SignedInteger);
    CHECK(value.integer == 19248);
}

TEST_CASE("Signed integer literal (overflow)", "[lexer]") {
    auto text = "9999999999";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::SignedLiteralTooLarge);

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::SignedInteger);
    CHECK(value.integer == 2147483647);
}

TEST_CASE("Real literal (fraction)", "[lexer]") {
    auto text = "32.57";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(value.real == 32.57);
}

TEST_CASE("Real literal (missing fraction)", "[lexer]") {
    auto text = "32.";
    auto token = lexToken(text);

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
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    double a = 32e57;
    CHECK(withinUlp(value.real, 32e57));
}

TEST_CASE("Real literal (plus exponent)", "[lexer]") {
    auto text = "0000032e+00057";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(withinUlp(value.real, 32e+57));
}

TEST_CASE("Real literal (minus exponent)", "[lexer]") {
    auto text = "32e-57";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(withinUlp(value.real, 32e-57));
}

TEST_CASE("Real literal (fraction exponent)", "[lexer]") {
    auto text = "32.3456e57";
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(value.real == 32.3456e57);
}

TEST_CASE("Real literal (exponent overflow)", "[lexer]") {
    auto text = "32e9000";
    auto token = lexToken(text);

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
    auto token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::RealExponentTooLarge);

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(std::isinf(value.real));
}

void testPunctuation(TokenKind kind) {
    auto text = GetTokenKindText(kind);
    auto token = lexToken(std::string(text.begin(), text.end()));

    CHECK(token.kind == kind);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("All Punctuation", "[lexer]") {
    testPunctuation(TokenKind::ApostropheOpenBrace);
    testPunctuation(TokenKind::OpenBrace);
    testPunctuation(TokenKind::CloseBrace);
    testPunctuation(TokenKind::OpenBracket);
    testPunctuation(TokenKind::CloseBracket);
    testPunctuation(TokenKind::OpenParenthesis);
    testPunctuation(TokenKind::OpenParenthesisStar);
    testPunctuation(TokenKind::CloseParenthesis);
    testPunctuation(TokenKind::StarCloseParenthesis);
    testPunctuation(TokenKind::Semicolon);
    testPunctuation(TokenKind::Colon);
    testPunctuation(TokenKind::ColonEquals);
    testPunctuation(TokenKind::ColonSlash);
    testPunctuation(TokenKind::DoubleColon);
    testPunctuation(TokenKind::StarDoubleColonStar);
    testPunctuation(TokenKind::Comma);
    testPunctuation(TokenKind::DotStar);
    testPunctuation(TokenKind::Dot);
    testPunctuation(TokenKind::Slash);
    testPunctuation(TokenKind::Star);
    testPunctuation(TokenKind::DoubleStar);
    testPunctuation(TokenKind::StarArrow);
    testPunctuation(TokenKind::Plus);
    testPunctuation(TokenKind::DoublePlus);
    testPunctuation(TokenKind::PlusColon);
    testPunctuation(TokenKind::Minus);
    testPunctuation(TokenKind::DoubleMinus);
    testPunctuation(TokenKind::MinusColon);
    testPunctuation(TokenKind::MinusArrow);
    testPunctuation(TokenKind::MinusDoubleArrow);
    testPunctuation(TokenKind::Tilde);
    testPunctuation(TokenKind::TildeAnd);
    testPunctuation(TokenKind::TildeOr);
    testPunctuation(TokenKind::TildeXor);
    testPunctuation(TokenKind::Dollar);
    testPunctuation(TokenKind::Question);
    testPunctuation(TokenKind::Hash);
    testPunctuation(TokenKind::DoubleHash);
    testPunctuation(TokenKind::HashMinusHash);
    testPunctuation(TokenKind::HashEqualsHash);
    testPunctuation(TokenKind::Xor);
    testPunctuation(TokenKind::XorTilde);
    testPunctuation(TokenKind::Equals);
    testPunctuation(TokenKind::DoubleEquals);
    testPunctuation(TokenKind::DoubleEqualsQuestion);
    testPunctuation(TokenKind::TripleEquals);
    testPunctuation(TokenKind::EqualsArrow);
    testPunctuation(TokenKind::PlusEqual);
    testPunctuation(TokenKind::MinusEqual);
    testPunctuation(TokenKind::SlashEqual);
    testPunctuation(TokenKind::StarEqual);
    testPunctuation(TokenKind::AndEqual);
    testPunctuation(TokenKind::OrEqual);
    testPunctuation(TokenKind::PercentEqual);
    testPunctuation(TokenKind::XorEqual);
    testPunctuation(TokenKind::LeftShiftEqual);
    testPunctuation(TokenKind::TripleLeftShiftEqual);
    testPunctuation(TokenKind::RightShiftEqual);
    testPunctuation(TokenKind::TripleRightShiftEqual);
    testPunctuation(TokenKind::LeftShift);
    testPunctuation(TokenKind::RightShift);
    testPunctuation(TokenKind::TripleLeftShift);
    testPunctuation(TokenKind::TripleRightShift);
    testPunctuation(TokenKind::Exclamation);
    testPunctuation(TokenKind::ExclamationEquals);
    testPunctuation(TokenKind::ExclamationEqualsQuestion);
    testPunctuation(TokenKind::ExclamationDoubleEquals);
    testPunctuation(TokenKind::Percent);
    testPunctuation(TokenKind::LessThan);
    testPunctuation(TokenKind::LessThanEquals);
    testPunctuation(TokenKind::LessThanMinusArrow);
    testPunctuation(TokenKind::GreaterThan);
    testPunctuation(TokenKind::GreaterThanEquals);
    testPunctuation(TokenKind::Or);
    testPunctuation(TokenKind::DoubleOr);
    testPunctuation(TokenKind::OrMinusArrow);
    testPunctuation(TokenKind::OrEqualsArrow);
    testPunctuation(TokenKind::At);
    testPunctuation(TokenKind::DoubleAt);
    testPunctuation(TokenKind::And);
    testPunctuation(TokenKind::DoubleAnd);
    testPunctuation(TokenKind::TripleAnd);
}