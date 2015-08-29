#include "catch.hpp"
#include "slang.h"

using namespace std::literals::string_literals;
using namespace slang;

Allocator pool;

const Token& LexToken(const std::string& text) {
    Lexer lexer(text.c_str(), pool);
    Token* token = lexer.Lex();
    REQUIRE(token != nullptr);
    return *token;
}

TEST_CASE("Line Comment", "[lexer]") {
    auto text = "// comment";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.trivia.Count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::LineComment);
}

TEST_CASE("Block Comment (one line)", "[lexer]") {
    auto text = "/* comment */";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.trivia.Count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::BlockComment);
}

TEST_CASE("Block Comment (multiple lines)", "[lexer]") {
    auto text =
R"(/*
comment on
multiple lines
*/)";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.trivia.Count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::BlockComment);
}

TEST_CASE("Whitespace", "[lexer]") {
    auto text = " \t\v\f token";
    auto token = LexToken(text);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.trivia.Count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::Whitespace);
}

TEST_CASE("Newlines", "[lexer]") {
    auto text = "\r";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.trivia.Count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::EndOfLine);

    text = "\r\n";
    token = LexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.trivia.Count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::EndOfLine);

    text = "\n";
    token = LexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.trivia.Count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::EndOfLine);
}

TEST_CASE("Simple Identifiers", "[lexer]") {
    auto text = "a";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::Identifier);

    text = "abc";
    token = LexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
}

TEST_CASE("Mixed Identifiers", "[lexer]") {
    auto text = "a92837asdf358";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::Identifier);

    text = "__a$$asdf213$";
    token = LexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
}

TEST_CASE("Escaped Identifiers", "[lexer]") {
    auto text = "\\98\\#$%)(*lkjsd__09...asdf345";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
}

TEST_CASE("System Identifiers", "[lexer]") {
    auto text = "$hello";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::SystemIdentifier);

    text = "$45__hello";
    token = LexToken(text);
    CHECK(token.kind == TokenKind::SystemIdentifier);
}

TEST_CASE("String Literal", "[lexer]") {
    auto text = "\"literal\"";
    auto token = LexToken(text);
    CHECK(token.kind == TokenKind::StringLiteral);
}

void TestPunctuation(TokenKind kind) {
    auto text = GetTokenKindText(kind);
    auto token = LexToken(text);
    CHECK(token.kind == kind);
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