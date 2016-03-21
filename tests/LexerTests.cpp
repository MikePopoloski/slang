#include "catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

BumpAllocator alloc;
Diagnostics diagnostics;
SourceTracker sourceTracker;

bool withinUlp(double a, double b) {
    return std::abs(((int64_t)a - (int64_t)b)) <= 1;
}

const Token& lexToken(const SourceText& text) {
    diagnostics.clear();
    Lexer lexer(FileID(), text, alloc, diagnostics);

    Token* token = lexer.lex();
    REQUIRE(token != nullptr);
    return *token;
}

TEST_CASE("Invalid chars", "[lexer]") {
    auto& text = "\x04";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::Unknown);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::NonPrintableChar);
}

TEST_CASE("UTF8 chars", "[lexer]") {
    auto& text = u8"\U0001f34c";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::Unknown);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::UTF8Char);
}

TEST_CASE("Unicode BOMs", "[lexer]") {
    lexToken("\xEF\xBB\xBF ");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::UnicodeBOM);

    lexToken("\xFE\xFF ");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::UnicodeBOM);

    lexToken("\xFF\xFE ");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::UnicodeBOM);
}

TEST_CASE("Embedded null", "[lexer]") {
    const char text[] = "\0";
    auto str = std::string(text, text + sizeof(text) - 1);
    auto& token = lexToken(str);

    CHECK(token.kind == TokenKind::Unknown);
    CHECK(token.toFullString() == str);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::EmbeddedNull);
}

TEST_CASE("Line Comment", "[lexer]") {
    auto& text = "// comment";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::LineComment);
    CHECK(diagnostics.empty());
}

TEST_CASE("Block Comment (one line)", "[lexer]") {
    auto& text = "/* comment */";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::BlockComment);
    CHECK(diagnostics.empty());
}

TEST_CASE("Block Comment (multiple lines)", "[lexer]") {
    auto& text =
        R"(/*
comment on
multiple lines
*/)";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::BlockComment);
    CHECK(diagnostics.empty());
}

TEST_CASE("Block Comment (unterminated)", "[lexer]") {
    auto& text = "/* comment";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::BlockComment);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::UnterminatedBlockComment);
}

TEST_CASE("Block Comment (nested)", "[lexer]") {
    auto& text = "/* comment /* stuff */";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::BlockComment);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::NestedBlockComment);
}

TEST_CASE("Whitespace", "[lexer]") {
    auto& text = " \t\v\f token";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::Whitespace);
    CHECK(diagnostics.empty());
}

TEST_CASE("Newlines (CR)", "[lexer]") {
    auto& text = "\r";
    auto& token = lexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::EndOfLine);
    CHECK(diagnostics.empty());
}

TEST_CASE("Newlines (CR/LF)", "[lexer]") {
    auto& text = "\r\n";
    auto& token = lexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::EndOfLine);
    CHECK(diagnostics.empty());
}

TEST_CASE("Newlines (LF)", "[lexer]") {
    auto& text = "\n";
    auto& token = lexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toFullString() == text);
    CHECK(token.trivia.count() == 1);
    CHECK(token.trivia[0].kind == TriviaKind::EndOfLine);
    CHECK(diagnostics.empty());
}

TEST_CASE("Simple Identifiers", "[lexer]") {
    auto& text = "abc";
    auto& token = lexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == text);
    CHECK(token.identifierType() == IdentifierType::Normal);
    CHECK(diagnostics.empty());
}

TEST_CASE("Mixed Identifiers", "[lexer]") {
    auto& text = "a92837asdf358";
    auto& token = lexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == text);
    CHECK(token.identifierType() == IdentifierType::Normal);
    CHECK(diagnostics.empty());

    auto& text2 = "__a$$asdf213$";
    auto& token2 = lexToken(text2);
    CHECK(token2.kind == TokenKind::Identifier);
    CHECK(token2.toFullString() == text2);
    CHECK(token2.valueText() == text2);
    CHECK(token2.identifierType() == IdentifierType::Normal);
    CHECK(diagnostics.empty());
}

TEST_CASE("Escaped Identifiers", "[lexer]") {
    auto& text = "\\98\\#$%)(*lkjsd__09...asdf345";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "98\\#$%)(*lkjsd__09...asdf345");
    CHECK(token.identifierType() == IdentifierType::Escaped);
    CHECK(diagnostics.empty());
}

TEST_CASE("System Identifiers", "[lexer]") {
    auto& text = "$hello";
    auto& token = lexToken(text);
    CHECK(token.kind == TokenKind::SystemIdentifier);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == text);
    CHECK(token.identifierType() == IdentifierType::System);
    CHECK(diagnostics.empty());

    auto& text2 = "$45__hello";
    auto& token2 = lexToken(text2);
    CHECK(token2.kind == TokenKind::SystemIdentifier);
    CHECK(token2.toFullString() == text2);
    CHECK(token2.valueText() == text2);
    CHECK(token2.identifierType() == IdentifierType::System);
    CHECK(diagnostics.empty());
}

TEST_CASE("Invalid escapes", "[lexer]") {
    auto& text = "\\";
    auto& token = lexToken(text);
    CHECK(token.kind == TokenKind::Unknown);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::EscapedWhitespace);

    auto& token2 = lexToken("\\  ");
    CHECK(token2.kind == TokenKind::Unknown);
    CHECK(token2.toString() == "\\");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::EscapedWhitespace);
}

TEST_CASE("String literal", "[lexer]") {
    auto& text = "\"literal  #@$asdf\"";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal  #@$asdf");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (newline)", "[lexer]") {
    auto& text = "\"literal\r\nwith new line\"";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() != text);
    CHECK(token.valueText() == "literal");

    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::NewlineInStringLiteral);
}

TEST_CASE("String literal (escaped newline)", "[lexer]") {
    auto& text = "\"literal\\\r\nwith new line\"";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literalwith new line");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (unterminated)", "[lexer]") {
    auto& text = "\"literal";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal");

    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::UnterminatedStringLiteral);
}

TEST_CASE("String literal (escapes)", "[lexer]") {
    auto& text = "\"literal\\n\\t\\v\\f\\a \\\\ \\\" \"";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal\n\t\v\f\a \\ \" ");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (octal escape)", "[lexer]") {
    auto& text = "\"literal\\377\"";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal\377");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (bad octal escape)", "[lexer]") {
    auto& text = "\"literal\\400\"";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::OctalEscapeCodeTooBig);
}

TEST_CASE("String literal with hex escape", "[lexer]") {
    auto& text = "\"literal\\xFa\"";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literal\xFa");
    CHECK(diagnostics.empty());
}

TEST_CASE("String literal (bad hex escape)", "[lexer]") {
    auto& text = "\"literal\\xz\"";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literalz");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::InvalidHexEscapeCode);
}

TEST_CASE("String literal (unknown escape)", "[lexer]") {
    auto& text = "\"literal\\i\"";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == "literali");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::UnknownEscapeCode);
}

TEST_CASE("Signed integer literal", "[lexer]") {
    auto& text = "19248";
    auto& token = lexToken(text);

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
    auto& text = "192__48         \v\t ";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toString() != text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::SignedInteger);
    CHECK(value.integer == 19248);
}

TEST_CASE("Signed integer literal (overflow)", "[lexer]") {
    auto& text = "9999999999";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::SignedLiteralTooLarge);

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::SignedInteger);
    CHECK(value.integer == 2147483647);
}

TEST_CASE("Real literal (fraction)", "[lexer]") {
    auto& text = "32.57";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(value.real == 32.57);
}

TEST_CASE("Real literal (missing fraction)", "[lexer]") {
    auto& text = "32.";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::MissingFractionalDigits);

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(value.real == 32);
}

TEST_CASE("Real literal (exponent)", "[lexer]") {
    auto& text = "32e57";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    double a = 32e57;
    CHECK(withinUlp(value.real, 32e57));
}

TEST_CASE("Real literal (plus exponent)", "[lexer]") {
    auto& text = "0000032E+00057";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(withinUlp(value.real, 32e+57));
}

TEST_CASE("Real literal (minus exponent)", "[lexer]") {
    auto& text = "32e-57";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(withinUlp(value.real, 32e-57));
}

TEST_CASE("Real literal (fraction exponent)", "[lexer]") {
    auto& text = "32.3456e57";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(value.real == 32.3456e57);
}

TEST_CASE("Real literal (bad exponent)", "[lexer]") {
    auto& text = "32ez";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == "32e");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::MissingExponentDigits);

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(value.real == 32);
}

TEST_CASE("Real literal (exponent overflow)", "[lexer]") {
    auto& text = "32e9000";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::RealExponentTooLarge);

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(std::isinf(value.real));
}

TEST_CASE("Real literal (digit overflow)", "[lexer]") {
    auto& text = std::string(400, '9') + ".0";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::RealExponentTooLarge);

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Real);
    CHECK(std::isinf(value.real));
}

TEST_CASE("Vector literal (zero size)", "[lexer]") {
    auto& text = "0'd34";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::IntegerSizeZero);
}

TEST_CASE("Vector literal (size overflow)", "[lexer]") {
    auto& text = "9999999999999999999'd34";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::IntegerSizeTooLarge);
}

TEST_CASE("Vector literal (missing base)", "[lexer]") {
    auto& text = "12'34";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == "12'");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::MissingVectorBase);
}

TEST_CASE("Decimal vector literal", "[lexer]") {
    auto& text = "123'd34_562xXz??";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Vector);
    //CHECK(value.integer == 19248);
}

TEST_CASE("Decimal vector literal (with whitespace)", "[lexer]") {
    auto& text = "123   'D   34_562xXz??";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Vector);
    //CHECK(value.integer == 19248);
}

TEST_CASE("Decimal vector literal (missing digits)", "[lexer]") {
    auto& text = "4'dggg";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == "4'd");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::MissingVectorDigits);
}

TEST_CASE("Decimal vector literal (unsized)", "[lexer]") {
    auto& text = "'d34_562xXz??";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Vector);
    //CHECK(value.integer == 19248);
}

TEST_CASE("Octal vector literal", "[lexer]") {
    auto& text = "123'o34_562xXz??";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Vector);
    //CHECK(value.integer == 19248);
}

TEST_CASE("Octal vector literal (with whitespace)", "[lexer]") {
    auto& text = "123   'O   34_562xXz??";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Vector);
    //CHECK(value.integer == 19248);
}

TEST_CASE("Octal vector literal (missing digits)", "[lexer]") {
    auto& text = "4'o9";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == "4'o");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::MissingVectorDigits);
}

TEST_CASE("Octal vector literal (unsized)", "[lexer]") {
    auto& text = "'o34_562xXz??";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Vector);
    //CHECK(value.integer == 19248);
}

TEST_CASE("Hex vector literal", "[lexer]") {
    auto& text = "123'h3f4_56aA02xXz??";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Vector);
    //CHECK(value.integer == 19248);
}

TEST_CASE("Hex vector literal (with whitespace)", "[lexer]") {
    auto& text = "123   'H   ffF_a562xXz??";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Vector);
    //CHECK(value.integer == 19248);
}

TEST_CASE("Hex vector literal (missing digits)", "[lexer]") {
    auto& text = "4'hG";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == "4'h");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::MissingVectorDigits);
}

TEST_CASE("Hex vector literal (unsized)", "[lexer]") {
    auto& text = "'h3f4_56aA02xXz??";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Vector);
    //CHECK(value.integer == 19248);
}

TEST_CASE("Binary vector literal", "[lexer]") {
    auto& text = "123'b1101_xX?zZ";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Vector);
    //CHECK(value.integer == 19248);
}

TEST_CASE("Binary vector literal (with whitespace)", "[lexer]") {
    auto& text = "123   'B   1101_xX??zZ";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Vector);
    //CHECK(value.integer == 19248);
}

TEST_CASE("Binary vector literal (missing digits)", "[lexer]") {
    auto& text = "4'b2";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == "4'b");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::MissingVectorDigits);
}

TEST_CASE("Binary vector literal (unsized)", "[lexer]") {
    auto& text = "'b1101_xX?zZ";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::Vector);
    //CHECK(value.integer == 19248);
}

void testTimeLiteral(uint8_t type, std::string text) {
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::TimeLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.isTimeValue());
    CHECK(value.type == type);
}

TEST_CASE("Time literals", "[lexer]") {
    testTimeLiteral(NumericValue::Seconds, "32.3s");
    testTimeLiteral(NumericValue::Milliseconds, "49ms");
    testTimeLiteral(NumericValue::Microseconds, "109.109us");
    testTimeLiteral(NumericValue::Nanoseconds, "17ns");
    testTimeLiteral(NumericValue::Picoseconds, "17ps");
    testTimeLiteral(NumericValue::Femtoseconds, "17fs");
}

TEST_CASE("Unsized unbased literal", "[lexer]") {
    auto& text = "'1";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toFullString() == text);
    CHECK(diagnostics.empty());

    auto& value = token.numericValue();
    CHECK(value.type == NumericValue::UnsizedBit);
    //CHECK(value.integer == 19248);
}

TEST_CASE("Misplaced directive char", "[lexer]") {
    auto& text = "`";
    auto& token = lexToken(text);

    CHECK(token.kind == TokenKind::Directive);
	CHECK(token.directiveKind() == SyntaxKind::Unknown);
    CHECK(token.toFullString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.last().code == DiagCode::MisplacedDirectiveChar);
}

void testKeyword(TokenKind kind) {
    auto text = getTokenKindText(kind);
    auto& token = lexToken(SourceText::fromNullTerminated(text));

    CHECK(token.kind == kind);
    CHECK(token.toFullString() == text);
    CHECK(token.valueText() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("All Keywords", "[preprocessor]") {
    testKeyword(TokenKind::OneStep);
    testKeyword(TokenKind::AcceptOnKeyword);
    testKeyword(TokenKind::AliasKeyword);
    testKeyword(TokenKind::AlwaysKeyword);
    testKeyword(TokenKind::AlwaysCombKeyword);
    testKeyword(TokenKind::AlwaysFFKeyword);
    testKeyword(TokenKind::AlwaysLatchKeyword);
    testKeyword(TokenKind::AndKeyword);
    testKeyword(TokenKind::AssertKeyword);
    testKeyword(TokenKind::AssignKeyword);
    testKeyword(TokenKind::AssumeKeyword);
    testKeyword(TokenKind::AutomaticKeyword);
    testKeyword(TokenKind::BeforeKeyword);
    testKeyword(TokenKind::BeginKeyword);
    testKeyword(TokenKind::BindKeyword);
    testKeyword(TokenKind::BinsKeyword);
    testKeyword(TokenKind::BinsOfKeyword);
    testKeyword(TokenKind::BitKeyword);
    testKeyword(TokenKind::BreakKeyword);
    testKeyword(TokenKind::BufKeyword);
    testKeyword(TokenKind::BufIf0Keyword);
    testKeyword(TokenKind::BufIf1Keyword);
    testKeyword(TokenKind::ByteKeyword);
    testKeyword(TokenKind::CaseKeyword);
    testKeyword(TokenKind::CaseXKeyword);
    testKeyword(TokenKind::CaseZKeyword);
    testKeyword(TokenKind::CellKeyword);
    testKeyword(TokenKind::CHandleKeyword);
    testKeyword(TokenKind::CheckerKeyword);
    testKeyword(TokenKind::ClassKeyword);
    testKeyword(TokenKind::ClockingKeyword);
    testKeyword(TokenKind::CmosKeyword);
    testKeyword(TokenKind::ConfigKeyword);
    testKeyword(TokenKind::ConstKeyword);
    testKeyword(TokenKind::ConstraintKeyword);
    testKeyword(TokenKind::ContextKeyword);
    testKeyword(TokenKind::ContinueKeyword);
    testKeyword(TokenKind::CoverKeyword);
    testKeyword(TokenKind::CoverGroupKeyword);
    testKeyword(TokenKind::CoverPointKeyword);
    testKeyword(TokenKind::CrossKeyword);
    testKeyword(TokenKind::DeassignKeyword);
    testKeyword(TokenKind::DefaultKeyword);
    testKeyword(TokenKind::DefParamKeyword);
    testKeyword(TokenKind::DesignKeyword);
    testKeyword(TokenKind::DisableKeyword);
    testKeyword(TokenKind::DistKeyword);
    testKeyword(TokenKind::DoKeyword);
    testKeyword(TokenKind::EdgeKeyword);
    testKeyword(TokenKind::ElseKeyword);
    testKeyword(TokenKind::EndKeyword);
    testKeyword(TokenKind::EndCaseKeyword);
    testKeyword(TokenKind::EndCheckerKeyword);
    testKeyword(TokenKind::EndClassKeyword);
    testKeyword(TokenKind::EndClockingKeyword);
    testKeyword(TokenKind::EndConfigKeyword);
    testKeyword(TokenKind::EndFunctionKeyword);
    testKeyword(TokenKind::EndGenerateKeyword);
    testKeyword(TokenKind::EndGroupKeyword);
    testKeyword(TokenKind::EndInterfaceKeyword);
    testKeyword(TokenKind::EndModuleKeyword);
    testKeyword(TokenKind::EndPackageKeyword);
    testKeyword(TokenKind::EndPrimitiveKeyword);
    testKeyword(TokenKind::EndProgramKeyword);
    testKeyword(TokenKind::EndPropertyKeyword);
    testKeyword(TokenKind::EndSpecifyKeyword);
    testKeyword(TokenKind::EndSequenceKeyword);
    testKeyword(TokenKind::EndTableKeyword);
    testKeyword(TokenKind::EndTaskKeyword);
    testKeyword(TokenKind::EnumKeyword);
    testKeyword(TokenKind::EventKeyword);
    testKeyword(TokenKind::EventuallyKeyword);
    testKeyword(TokenKind::ExpectKeyword);
    testKeyword(TokenKind::ExportKeyword);
    testKeyword(TokenKind::ExtendsKeyword);
    testKeyword(TokenKind::ExternKeyword);
    testKeyword(TokenKind::FinalKeyword);
    testKeyword(TokenKind::FirstMatchKeyword);
    testKeyword(TokenKind::ForKeyword);
    testKeyword(TokenKind::ForceKeyword);
    testKeyword(TokenKind::ForeachKeyword);
    testKeyword(TokenKind::ForeverKeyword);
    testKeyword(TokenKind::ForkKeyword);
    testKeyword(TokenKind::ForkJoinKeyword);
    testKeyword(TokenKind::FunctionKeyword);
    testKeyword(TokenKind::GenerateKeyword);
    testKeyword(TokenKind::GenVarKeyword);
    testKeyword(TokenKind::GlobalKeyword);
    testKeyword(TokenKind::HighZ0Keyword);
    testKeyword(TokenKind::HighZ1Keyword);
    testKeyword(TokenKind::IfKeyword);
    testKeyword(TokenKind::IffKeyword);
    testKeyword(TokenKind::IfNoneKeyword);
    testKeyword(TokenKind::IgnoreBinsKeyword);
    testKeyword(TokenKind::IllegalBinsKeyword);
    testKeyword(TokenKind::ImplementsKeyword);
    testKeyword(TokenKind::ImpliesKeyword);
    testKeyword(TokenKind::ImportKeyword);
    testKeyword(TokenKind::IncDirKeyword);
    testKeyword(TokenKind::IncludeKeyword);
    testKeyword(TokenKind::InitialKeyword);
    testKeyword(TokenKind::InOutKeyword);
    testKeyword(TokenKind::InputKeyword);
    testKeyword(TokenKind::InsideKeyword);
    testKeyword(TokenKind::InstanceKeyword);
    testKeyword(TokenKind::IntKeyword);
    testKeyword(TokenKind::IntegerKeyword);
    testKeyword(TokenKind::InterconnectKeyword);
    testKeyword(TokenKind::InterfaceKeyword);
    testKeyword(TokenKind::IntersectKeyword);
    testKeyword(TokenKind::JoinKeyword);
    testKeyword(TokenKind::JoinAnyKeyword);
    testKeyword(TokenKind::JoinNoneKeyword);
    testKeyword(TokenKind::LargeKeyword);
    testKeyword(TokenKind::LetKeyword);
    testKeyword(TokenKind::LibListKeyword);
    testKeyword(TokenKind::LibraryKeyword);
    testKeyword(TokenKind::LocalKeyword);
    testKeyword(TokenKind::LocalParamKeyword);
    testKeyword(TokenKind::LogicKeyword);
    testKeyword(TokenKind::LongIntKeyword);
    testKeyword(TokenKind::MacromoduleKeyword);
    testKeyword(TokenKind::MatchesKeyword);
    testKeyword(TokenKind::MediumKeyword);
    testKeyword(TokenKind::ModPortKeyword);
    testKeyword(TokenKind::ModuleKeyword);
    testKeyword(TokenKind::NandKeyword);
    testKeyword(TokenKind::NegEdgeKeyword);
    testKeyword(TokenKind::NetTypeKeyword);
    testKeyword(TokenKind::NewKeyword);
    testKeyword(TokenKind::NextTimeKeyword);
    testKeyword(TokenKind::NmosKeyword);
    testKeyword(TokenKind::NorKeyword);
    testKeyword(TokenKind::NoShowCancelledKeyword);
    testKeyword(TokenKind::NotKeyword);
    testKeyword(TokenKind::NotIf0Keyword);
    testKeyword(TokenKind::NotIf1Keyword);
    testKeyword(TokenKind::NullKeyword);
    testKeyword(TokenKind::OrKeyword);
    testKeyword(TokenKind::OutputKeyword);
    testKeyword(TokenKind::PackageKeyword);
    testKeyword(TokenKind::PackedKeyword);
    testKeyword(TokenKind::ParameterKeyword);
    testKeyword(TokenKind::PmosKeyword);
    testKeyword(TokenKind::PosEdgeKeyword);
    testKeyword(TokenKind::PrimitiveKeyword);
    testKeyword(TokenKind::PriorityKeyword);
    testKeyword(TokenKind::ProgramKeyword);
    testKeyword(TokenKind::PropertyKeyword);
    testKeyword(TokenKind::ProtectedKeyword);
    testKeyword(TokenKind::Pull0Keyword);
    testKeyword(TokenKind::Pull1Keyword);
    testKeyword(TokenKind::PullDownKeyword);
    testKeyword(TokenKind::PullUpKeyword);
    testKeyword(TokenKind::PulseStyleOnDetectKeyword);
    testKeyword(TokenKind::PulseStyleOnEventKeyword);
    testKeyword(TokenKind::PureKeyword);
    testKeyword(TokenKind::RandKeyword);
    testKeyword(TokenKind::RandCKeyword);
    testKeyword(TokenKind::RandCaseKeyword);
    testKeyword(TokenKind::RandSequenceKeyword);
    testKeyword(TokenKind::RcmosKeyword);
    testKeyword(TokenKind::RealKeyword);
    testKeyword(TokenKind::RealTimeKeyword);
    testKeyword(TokenKind::RefKeyword);
    testKeyword(TokenKind::RegKeyword);
    testKeyword(TokenKind::RejectOnKeyword);
    testKeyword(TokenKind::ReleaseKeyword);
    testKeyword(TokenKind::RepeatKeyword);
    testKeyword(TokenKind::RestrictKeyword);
    testKeyword(TokenKind::ReturnKeyword);
    testKeyword(TokenKind::RnmosKeyword);
    testKeyword(TokenKind::RpmosKeyword);
    testKeyword(TokenKind::RtranKeyword);
    testKeyword(TokenKind::RtranIf0Keyword);
    testKeyword(TokenKind::RtranIf1Keyword);
    testKeyword(TokenKind::SAlwaysKeyword);
    testKeyword(TokenKind::SEventuallyKeyword);
    testKeyword(TokenKind::SNextTimeKeyword);
    testKeyword(TokenKind::SUntilKeyword);
    testKeyword(TokenKind::SUntilWithKeyword);
    testKeyword(TokenKind::ScalaredKeyword);
    testKeyword(TokenKind::SequenceKeyword);
    testKeyword(TokenKind::ShortIntKeyword);
    testKeyword(TokenKind::ShortRealKeyword);
    testKeyword(TokenKind::ShowCancelledKeyword);
    testKeyword(TokenKind::SignedKeyword);
    testKeyword(TokenKind::SmallKeyword);
    testKeyword(TokenKind::SoftKeyword);
    testKeyword(TokenKind::SolveKeyword);
    testKeyword(TokenKind::SpecifyKeyword);
    testKeyword(TokenKind::SpecParamKeyword);
    testKeyword(TokenKind::StaticKeyword);
    testKeyword(TokenKind::StringKeyword);
    testKeyword(TokenKind::StrongKeyword);
    testKeyword(TokenKind::Strong0Keyword);
    testKeyword(TokenKind::Strong1Keyword);
    testKeyword(TokenKind::StructKeyword);
    testKeyword(TokenKind::SuperKeyword);
    testKeyword(TokenKind::Supply0Keyword);
    testKeyword(TokenKind::Supply1Keyword);
    testKeyword(TokenKind::SyncAcceptOnKeyword);
    testKeyword(TokenKind::SyncRejectOnKeyword);
    testKeyword(TokenKind::TableKeyword);
    testKeyword(TokenKind::TaggedKeyword);
    testKeyword(TokenKind::TaskKeyword);
    testKeyword(TokenKind::ThisKeyword);
    testKeyword(TokenKind::ThroughoutKeyword);
    testKeyword(TokenKind::TimeKeyword);
    testKeyword(TokenKind::TimePrecisionKeyword);
    testKeyword(TokenKind::TimeUnitKeyword);
    testKeyword(TokenKind::TranKeyword);
    testKeyword(TokenKind::TranIf0Keyword);
    testKeyword(TokenKind::TranIf1Keyword);
    testKeyword(TokenKind::TriKeyword);
    testKeyword(TokenKind::Tri0Keyword);
    testKeyword(TokenKind::Tri1Keyword);
    testKeyword(TokenKind::TriAndKeyword);
    testKeyword(TokenKind::TriOrKeyword);
    testKeyword(TokenKind::TriRegKeyword);
    testKeyword(TokenKind::TypeKeyword);
    testKeyword(TokenKind::TypedefKeyword);
    testKeyword(TokenKind::UnionKeyword);
    testKeyword(TokenKind::UniqueKeyword);
    testKeyword(TokenKind::Unique0Keyword);
    testKeyword(TokenKind::UnsignedKeyword);
    testKeyword(TokenKind::UntilKeyword);
    testKeyword(TokenKind::UntilWithKeyword);
    testKeyword(TokenKind::UntypedKeyword);
    testKeyword(TokenKind::UseKeyword);
    testKeyword(TokenKind::UWireKeyword);
    testKeyword(TokenKind::VarKeyword);
    testKeyword(TokenKind::VectoredKeyword);
    testKeyword(TokenKind::VirtualKeyword);
    testKeyword(TokenKind::VoidKeyword);
    testKeyword(TokenKind::WaitKeyword);
    testKeyword(TokenKind::WaitOrderKeyword);
    testKeyword(TokenKind::WAndKeyword);
    testKeyword(TokenKind::WeakKeyword);
    testKeyword(TokenKind::Weak0Keyword);
    testKeyword(TokenKind::Weak1Keyword);
    testKeyword(TokenKind::WhileKeyword);
    testKeyword(TokenKind::WildcardKeyword);
    testKeyword(TokenKind::WireKeyword);
    testKeyword(TokenKind::WithKeyword);
    testKeyword(TokenKind::WithinKeyword);
    testKeyword(TokenKind::WOrKeyword);
    testKeyword(TokenKind::XnorKeyword);
    testKeyword(TokenKind::XorKeyword);
}

void testPunctuation(TokenKind kind) {
    auto& text = getTokenKindText(kind);
    auto& token = lexToken(SourceText::fromNullTerminated(text));

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
    testPunctuation(TokenKind::OpenParenthesisStarCloseParenthesis);
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
    testPunctuation(TokenKind::OrMinusDoubleArrow);
    testPunctuation(TokenKind::OrEqualsArrow);
    testPunctuation(TokenKind::At);
    testPunctuation(TokenKind::AtStar);
    testPunctuation(TokenKind::DoubleAt);
    testPunctuation(TokenKind::And);
    testPunctuation(TokenKind::DoubleAnd);
    testPunctuation(TokenKind::TripleAnd);
}

void testDirectivePunctuation(TokenKind kind) {
    auto& text = getTokenKindText(kind);

    diagnostics.clear();
    Lexer lexer(FileID(), SourceText::fromNullTerminated(text), alloc, diagnostics);

    Token* token = lexer.lex(LexerMode::Directive);

    CHECK(token->kind == kind);
    CHECK(token->toFullString() == text);
    CHECK(token->valueText() == text);
    CHECK(diagnostics.empty());
}

TEST_CASE("Directive Punctuation", "[lexer]") {
    testDirectivePunctuation(TokenKind::MacroQuote);
    testDirectivePunctuation(TokenKind::MacroEscapedQuote);
    testDirectivePunctuation(TokenKind::MacroPaste);
}

}