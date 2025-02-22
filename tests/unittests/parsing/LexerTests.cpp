// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Test.h"

#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/text/CharInfo.h"
#include "slang/text/SourceManager.h"

using LF = LexerFacts;

TEST_CASE("Invalid chars") {
    auto& text = "\x04";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::Unknown);
    CHECK(token.toString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::NonPrintableChar);
}

TEST_CASE("UTF8 chars") {
    auto& text = "\U0001f34c";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::Unknown);
    CHECK(token.toString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::UTF8Char);
}

TEST_CASE("Invalid UTF8 chars") {
    auto& text = "// asdf \xed\xa0\x80\xed\xa0\x80 asdf";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::InvalidUTF8Seq);
}

TEST_CASE("Unicode BOMs") {
    lexToken("\xEF\xBB\xBF ");
    REQUIRE(diagnostics.empty());

    lexToken("\xFE\xFF ");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::UnicodeBOM);

    lexToken("\xFF\xFE ");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::UnicodeBOM);
}

TEST_CASE("Embedded null") {
    const char text[] = "\0\0";
    auto str = std::string(text, text + sizeof(text) - 1);
    Token token = lexToken(str);

    CHECK(token.kind == TokenKind::Unknown);
    CHECK(token.toString() == str.substr(0, str.length() - 1));
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::EmbeddedNull);
}

TEST_CASE("Embedded null (string literal)") {
    const char text[] = "\"\0\"\0";
    auto str = std::string(text, text + sizeof(text) - 1);
    Token token = lexToken(str);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == str.substr(0, str.length() - 1));
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::EmbeddedNull);
}

TEST_CASE("Line Comment") {
    auto& text = "// comment";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == text);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::LineComment);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Line Comment (directive continuation)") {
    auto& text = "`define FOO // comment\\\n  bar";
    Token token = lexToken(text);

    std::string str = SyntaxPrinter().setIncludeDirectives(true).print(token).str();

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(str == text);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::Directive);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Line Comment (embedded null)") {
    const char text[] = "// foo \0 bar";
    auto str = std::string(text, text + sizeof(text) - 1);
    Token token = lexToken(str);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == str);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::LineComment);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::EmbeddedNull);
}

TEST_CASE("Line Comment (UTF8)") {
    const char text[] = "// foo 的氣墊船\u00F7\n";
    auto str = std::string(text, text + sizeof(text) - 1);
    Token token = lexToken(str);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == str);
    CHECK(token.trivia().size() == 2);
    CHECK(token.trivia()[0].kind == TriviaKind::LineComment);
    CHECK(token.trivia()[1].kind == TriviaKind::EndOfLine);
    REQUIRE(diagnostics.empty());
}

TEST_CASE("Embedded control characters in a broken UTF8 comment") {
    const char text[] = "//\xe0\x80\nendmodule";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndModuleKeyword);
    CHECK(token.trivia().size() == 2);
    CHECK(token.trivia()[0].kind == TriviaKind::LineComment);
    CHECK(token.trivia()[1].kind == TriviaKind::EndOfLine);
    REQUIRE(diagnostics.size() == 1); // Due to UTF8 intended error
}

TEST_CASE("Embedded control characters in a broken UTF8 comment (2)") {
    const char text[] = "//\x82\xe8\nendmodule";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndModuleKeyword);
    CHECK(token.trivia().size() == 2);
    CHECK(token.trivia()[0].kind == TriviaKind::LineComment);
    CHECK(token.trivia()[1].kind == TriviaKind::EndOfLine);
    REQUIRE(diagnostics.size() == 1); // Due to UTF8 intended error
}

TEST_CASE("Embedded control characters in a broken UTF8 comment not affecting lexer errorCount") {
    auto& text = "//\x82\xe8\n//\x82\xe8\n//\x82\xe8\n//\x82\xe8\n//\x82\xe8\n//\x82\xe8\n//"
                 "\x82\xe8\n//\x82\xe8\nendmodule\n";

    LexerOptions options;
    options.maxErrors = 4;

    diagnostics.clear();
    auto& sm = getSourceManager();
    auto buffer = sm.assignText(text);
    Lexer lexer(buffer, alloc, diagnostics, sm, options);
    Token token = lexer.lex();

    CHECK(token.kind == TokenKind::EndModuleKeyword);
    CHECK(token.trivia().size() == 16);
    for (int i = 0; i < 8; i++) {
        CHECK(token.trivia()[2 * i].kind == TriviaKind::LineComment);
        CHECK(token.trivia()[2 * i + 1].kind == TriviaKind::EndOfLine);
    }
    REQUIRE(diagnostics.size() == 8); // Due to UTF8 intended error
}

TEST_CASE("Block Comment (one line)") {
    auto& text = "/* comment */";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == text);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::BlockComment);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Block Comment (multiple lines)") {
    auto& text =
        R"(/*
comment on
multiple lines
*/)";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == text);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::BlockComment);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Block Comment (unterminated)") {
    auto& text = "/* comment";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == text);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::BlockComment);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::UnterminatedBlockComment);
}

TEST_CASE("Block comment (embedded null)") {
    const char text[] = "/* foo\0 */";
    auto str = std::string(text, text + sizeof(text) - 1);
    Token token = lexToken(str);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == str);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::BlockComment);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::EmbeddedNull);
}

TEST_CASE("Block comment (UTF8 text)") {
    const char text[] = "/* foo 的氣墊船 */";
    auto str = std::string(text, text + sizeof(text) - 1);
    Token token = lexToken(str);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == str);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::BlockComment);
    REQUIRE(diagnostics.empty());
}

TEST_CASE("Block Comment (nested)") {
    auto& text = "/* comment /* stuff */";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == text);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::BlockComment);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::NestedBlockComment);
}

TEST_CASE("Whitespace") {
    auto& text = " \t\v\f token";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toString() == text);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::Whitespace);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Newlines (CR)") {
    auto& text = "\r";
    Token token = lexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == text);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::EndOfLine);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Newlines (CR/LF)") {
    auto& text = "\r\n";
    Token token = lexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == text);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::EndOfLine);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Newlines (LF)") {
    auto& text = "\n";
    Token token = lexToken(text);
    CHECK(token.kind == TokenKind::EndOfFile);
    CHECK(token.toString() == text);
    CHECK(token.trivia().size() == 1);
    CHECK(token.trivia()[0].kind == TriviaKind::EndOfLine);
    CHECK(token.trivia()[0].syntax() == nullptr);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Simple Identifiers") {
    auto& text = "abc";
    Token token = lexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Mixed Identifiers") {
    auto& text = "a92837asdf358";
    Token token = lexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == text);
    CHECK_DIAGNOSTICS_EMPTY;

    auto& text2 = "__a$$asdf213$";
    Token token2 = lexToken(text2);
    CHECK(token2.kind == TokenKind::Identifier);
    CHECK(token2.toString() == text2);
    CHECK(token2.valueText() == text2);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Escaped Identifiers") {
    auto& text = "\\98\\#$%)(*lkjsd__09...asdf345";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == "98\\#$%)(*lkjsd__09...asdf345");
    CHECK_DIAGNOSTICS_EMPTY;

    auto& text2 = "\\98\\#$%)(*lkjsd__09...a sdf345";
    token = lexToken(text2);

    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "98\\#$%)(*lkjsd__09...a");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("System Identifiers") {
    auto& text = "$hello";
    Token token = lexToken(text);
    CHECK(token.kind == TokenKind::SystemIdentifier);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == text);
    CHECK_DIAGNOSTICS_EMPTY;

    auto& text2 = "$45__hello";
    Token token2 = lexToken(text2);
    CHECK(token2.kind == TokenKind::SystemIdentifier);
    CHECK(token2.toString() == text2);
    CHECK(token2.valueText() == text2);
    CHECK_DIAGNOSTICS_EMPTY;

    CHECK(token != token2);
}

TEST_CASE("Invalid escapes") {
    auto& text = "\\";
    Token token = lexToken(text);
    CHECK(token.kind == TokenKind::Unknown);
    CHECK(token.toString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::EscapedWhitespace);

    Token token2 = lexToken("\\  ");
    CHECK(token2.kind == TokenKind::Unknown);
    CHECK(token2.toString() == "\\");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::EscapedWhitespace);

    Token token3 = lexToken("`\\  ");
    CHECK(token3.kind == TokenKind::Unknown);
    CHECK(token3.toString() == "`\\");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::EscapedWhitespace);
}

TEST_CASE("String literal") {
    auto& text = "\"literal  #@$asdf\"";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == "literal  #@$asdf");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("String literal (newline)") {
    auto& text = "\"literal\r\nwith new line\"";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() != text);
    CHECK(token.valueText() == "literal");

    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::ExpectedClosingQuote);
}

TEST_CASE("String literal (escaped newline)") {
    auto& text = "\"literal\\\r\nwith new line\"";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == "literalwith new line");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("String literal (unterminated)") {
    auto& text = "\"literal";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == "literal");

    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::ExpectedClosingQuote);
}

TEST_CASE("String literal (escapes)") {
    auto& text = "\"literal\\n\\t\\v\\f\\a \\\\ \\\" \"";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == "literal\n\t\v\f\a \\ \" ");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("String literal (octal escape)") {
    auto& text = "\"literal\\377\"";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == "literal\377");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("String literal (bad octal escape)") {
    auto& text = "\"literal\\400\"";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == "literal");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::OctalEscapeCodeTooBig);
}

TEST_CASE("String literal with hex escape") {
    auto& text = "\"literal\\xFa\"";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == "literal\xFa");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("String literal (bad hex escape)") {
    auto& text = "\"literal\\xz\"";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == "literalxz");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::InvalidHexEscapeCode);
}

TEST_CASE("String literal (unknown escape)") {
    auto& text = "\"literal\\i\"";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == "literali");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::UnknownEscapeCode);
}

TEST_CASE("String literal (nonstandard escape)") {
    auto& text = "\"literal\\%\"";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == "literal%");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::NonstandardEscapeCode);
}

TEST_CASE("String literal (null escape)") {
    auto& text = "\"literal\\\0\"";
    auto str = std::string(text, text + sizeof(text) - 1);
    Token token = lexToken(str);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == str);
    CHECK(token.valueText() == "literal");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::EmbeddedNull);
}

TEST_CASE("String literal (UTF8 escape)") {
    auto& text = "\"literal\\\U0001f34c\"";
    auto str = std::string(text, text + sizeof(text) - 1);
    Token token = lexToken(str);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == str);
    CHECK(token.valueText() == "literal\U0001f34c");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::UnknownEscapeCode);
}

TEST_CASE("String literal (triple quoted)") {
    auto& text = R"("""Humpty Dumpty sat on a "wall".
Humpty Dumpty had a great fall.""")";

    Token token = lexToken(text, LanguageVersion::v1800_2023);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == R"(Humpty Dumpty sat on a "wall".
Humpty Dumpty had a great fall.)");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("String literal (triple quoted with escaped newline)") {
    auto& text = R"("""Humpty Dumpty sat on a "wall". \
Humpty Dumpty had a great fall.""")";

    Token token = lexToken(text, LanguageVersion::v1800_2023);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == R"(Humpty Dumpty sat on a "wall". Humpty Dumpty had a great fall.)");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("String literal (triple quoted wrong version)") {
    auto& text = R"("""Humpty Dumpty sat on a "wall".
Humpty Dumpty had a great fall.""")";

    Token token = lexToken(text, LanguageVersion::v1800_2017);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == R"(Humpty Dumpty sat on a "wall".
Humpty Dumpty had a great fall.)");
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics.back().code == diag::WrongLanguageVersion);
}

TEST_CASE("Integer literal") {
    auto& text = "19248";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toString() == text);
    CHECK(token.intValue() == 19248);
    CHECK_DIAGNOSTICS_EMPTY;
}

void checkVectorBase(const std::string& s, LiteralBase base, bool isSigned) {
    Token token = lexToken(s);

    CHECK(token.kind == TokenKind::IntegerBase);
    CHECK(token.toString() == s);
    CHECK(token.numericFlags().base() == base);
    CHECK(token.numericFlags().isSigned() == isSigned);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Vector bases") {
    checkVectorBase("'d", LiteralBase::Decimal, false);
    checkVectorBase("'sD", LiteralBase::Decimal, true);
    checkVectorBase("'Sb", LiteralBase::Binary, true);
    checkVectorBase("'B", LiteralBase::Binary, false);
    checkVectorBase("'so", LiteralBase::Octal, true);
    checkVectorBase("'O", LiteralBase::Octal, false);
    checkVectorBase("'h", LiteralBase::Hex, false);
    checkVectorBase("'SH", LiteralBase::Hex, true);
}

TEST_CASE("Unbased unsized literal") {
    auto& text = "'1";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::UnbasedUnsizedLiteral);
    CHECK(token.toString() == text);
    CHECK(token.bitValue().value == 1);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Real literal (fraction)") {
    auto& text = "32.57";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toString() == text);
    CHECK(withinUlp(token.realValue(), 32.57));
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Real literal (exponent)") {
    auto& text = "32e57";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toString() == text);
    CHECK(withinUlp(token.realValue(), 32e57));
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Real literal (plus exponent)") {
    auto& text = "0000032E+000__57";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toString() == text);
    CHECK(withinUlp(token.realValue(), 32e57));
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Real literal (minus exponent)") {
    auto& text = "3_2e-5__7";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toString() == text);
    CHECK(withinUlp(token.realValue(), 32e-57));
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Real literal (fraction exponent)") {
    auto& text = "32.3456e57";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toString() == text);
    CHECK(withinUlp(token.realValue(), 32.3456e57));
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Real literal (underscores)") {
    auto& text = "32._34__56e_57";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toString() == text);
    CHECK(withinUlp(token.realValue(), 32.3456e57));
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Real literal (exponent overflow)") {
    auto& text = "32e9000";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toString() == text);
    CHECK(std::isinf(token.realValue()));
    CHECK(token.numericFlags().outOfRange());
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Real literal (underflow)") {
    auto& text = "32e-9000";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toString() == text);
    CHECK(token.realValue() == 0);
    CHECK(token.numericFlags().outOfRange());
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Real literal (bad exponent)") {
    auto& text = "32.234e";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toString() == "32.234e");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Real literal (digit overflow)") {
    std::string text = std::string(400, '9') + ".0";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::RealLiteral);
    CHECK(token.toString() == text);
    CHECK_DIAGNOSTICS_EMPTY;

    CHECK(std::isinf(token.realValue()));
    CHECK(token.numericFlags().outOfRange());
}

TEST_CASE("Integer literal (not an exponent)") {
    auto& text = "32ef9";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::IntegerLiteral);
    CHECK(token.toString() == "32");
    CHECK_DIAGNOSTICS_EMPTY;
}

void checkTimeLiteral(const std::string& s, TimeUnit flagCheck, double num) {
    Token token = lexToken(s);

    CHECK(token.kind == TokenKind::TimeLiteral);
    CHECK(token.toString() == s);
    CHECK(token.numericFlags().unit() == flagCheck);
    CHECK(token.realValue() == num);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Time literals") {
    checkTimeLiteral("3.4s", TimeUnit::Seconds, 3.4);
    checkTimeLiteral("9999ms", TimeUnit::Milliseconds, 9999);
    checkTimeLiteral("572.234us", TimeUnit::Microseconds, 572.234);
    checkTimeLiteral("97ns", TimeUnit::Nanoseconds, 97);
    checkTimeLiteral("42ps", TimeUnit::Picoseconds, 42);
    checkTimeLiteral("42fs", TimeUnit::Femtoseconds, 42);
}

TEST_CASE("Bad time literal") {
    Token token = lexToken("10mX");
    CHECK(token.kind != TokenKind::TimeLiteral);
}

TEST_CASE("Colon") {
    SECTION("Basic Colon") {
        auto& text = ":";
        Token token = lexToken(text);

        CHECK(token.kind == TokenKind::Colon);
        CHECK(token.toString() == ":");
        CHECK_DIAGNOSTICS_EMPTY;
    }
    SECTION("Colon followed by comment") {
        auto& text = ":// comment";
        Token token = lexToken(text);

        CHECK(token.kind == TokenKind::Colon);
        CHECK(token.toString() == ":");
        CHECK_DIAGNOSTICS_EMPTY;
    }
    SECTION("Colon followed by another kind of comment") {
        auto& text = ":/* comment */";
        Token token = lexToken(text);

        CHECK(token.kind == TokenKind::Colon);
        CHECK(token.toString() == ":");
        CHECK_DIAGNOSTICS_EMPTY;
    }
}

TEST_CASE("Directive continuation") {
    auto& text = "`define FOO asdf\\\nbar\\\r\nbaz";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    REQUIRE(token.trivia().size() == 1);

    Trivia t = token.trivia()[0];
    CHECK(t.kind == TriviaKind::Directive);
    REQUIRE(t.syntax()->kind == SyntaxKind::DefineDirective);

    CHECK(t.getSkippedTokens().empty());
    CHECK(t.getRawText() == "");
    CHECK(t.withLocation(alloc, SourceLocation()).getExplicitLocation() == t.getExplicitLocation());

    const DefineDirectiveSyntax& define = t.syntax()->as<DefineDirectiveSyntax>();
    REQUIRE(define.body.size() == 5);
    CHECK(define.body[4].valueText() == "baz");

    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Escaped keyword identifiers") {
    auto& text = "\\wire";

    auto token = lexToken(text);
    CHECK(token.kind == TokenKind::Identifier);
    CHECK(token.valueText() == "wire");
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Too many errors") {
    std::vector<char> buf(10, '\x01');

    LexerOptions options;
    options.maxErrors = 9;

    diagnostics.clear();
    auto& sm = getSourceManager();
    auto buffer = sm.assignText(std::string_view(buf.data(), buf.size()));
    Lexer lexer(buffer, alloc, diagnostics, sm, options);

    for (size_t i = 0; i < buf.size() - 1; i++)
        CHECK(lexer.lex().kind == TokenKind::Unknown);

    CHECK(diagnostics.size() == buf.size() - 1);
    CHECK(lexer.lex().kind == TokenKind::EndOfFile);
    CHECK(diagnostics.back().code == diag::TooManyLexerErrors);
}

void testKeyword(TokenKind kind) {
    auto text = LF::getTokenKindText(kind);
    Token token = lexToken(text);

    CHECK(token.kind == kind);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("All Keywords") {
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
    std::string_view text = LF::getTokenKindText(kind);
    Token token = lexToken(text);

    CHECK(token.kind == kind);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("All Punctuation") {
    testPunctuation(TokenKind::ApostropheOpenBrace);
    testPunctuation(TokenKind::OpenBrace);
    testPunctuation(TokenKind::CloseBrace);
    testPunctuation(TokenKind::OpenBracket);
    testPunctuation(TokenKind::CloseBracket);
    testPunctuation(TokenKind::OpenParenthesis);
    testPunctuation(TokenKind::CloseParenthesis);
    testPunctuation(TokenKind::Semicolon);
    testPunctuation(TokenKind::Colon);
    testPunctuation(TokenKind::ColonEquals);
    testPunctuation(TokenKind::ColonSlash);
    testPunctuation(TokenKind::DoubleColon);
    testPunctuation(TokenKind::Comma);
    testPunctuation(TokenKind::Dot);
    testPunctuation(TokenKind::Slash);
    testPunctuation(TokenKind::Star);
    testPunctuation(TokenKind::DoubleStar);
    testPunctuation(TokenKind::StarArrow);
    testPunctuation(TokenKind::Plus);
    testPunctuation(TokenKind::DoublePlus);
    testPunctuation(TokenKind::PlusColon);
    testPunctuation(TokenKind::PlusDivMinus);
    testPunctuation(TokenKind::PlusModMinus);
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

void testDirectivePunctuation(TokenKind kind) {
    std::string_view text = LF::getTokenKindText(kind);

    diagnostics.clear();
    auto& sm = getSourceManager();
    auto buffer = sm.assignText(text);
    Lexer lexer(buffer, alloc, diagnostics, sm);

    Token token = lexer.lex();

    CHECK(token.kind == kind);
    CHECK(token.toString() == text);
    CHECK(token.valueText() == text);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Directive Punctuation") {
    testDirectivePunctuation(TokenKind::MacroQuote);
    testDirectivePunctuation(TokenKind::MacroTripleQuote);
    testDirectivePunctuation(TokenKind::MacroEscapedQuote);
    testDirectivePunctuation(TokenKind::MacroPaste);
}

TEST_CASE("Punctuation corner cases") {
    // These look like the start of a longer token but are not, so the
    // lexer needs to properly fallback to the original character.
    Token token = lexToken("#-");
    CHECK(token.kind == TokenKind::Hash);
    CHECK_DIAGNOSTICS_EMPTY;

    token = lexToken("#=");
    CHECK(token.kind == TokenKind::Hash);
    CHECK_DIAGNOSTICS_EMPTY;

    token = lexToken("*::");
    CHECK(token.kind == TokenKind::Star);
    CHECK_DIAGNOSTICS_EMPTY;

    token = lexToken("<-");
    CHECK(token.kind == TokenKind::LessThan);
    CHECK_DIAGNOSTICS_EMPTY;

    token = lexToken("|-");
    CHECK(token.kind == TokenKind::Or);
    CHECK_DIAGNOSTICS_EMPTY;
}

TEST_CASE("Skipped token inspection") {
    Token token = lexToken("`` foo");
    CHECK(token.kind == TokenKind::Identifier);

    auto trivia = token.trivia()[0];
    CHECK(trivia.getExplicitLocation() == token.location() - 3);
    CHECK(trivia.getSkippedTokens()[0].kind == TokenKind::MacroPaste);

    token = token.withRawText(alloc, "asdf");
    CHECK(token.rawText() == "asdf");
    CHECK(token.location() == *trivia.getExplicitLocation() + 3);
}

TEST_CASE("Token with lots of trivia") {
    Token token = lexToken(" /**/ /**/ /**/ /**/ /**/ /**/ /**/ foo");
    CHECK(token.kind == TokenKind::Identifier);
    REQUIRE(token.trivia().size() == 15);

    Trivia trivia = token.trivia()[3];
    CHECK(trivia.getRawText() == "/**/");
    CHECK(!trivia.getExplicitLocation().has_value());

    trivia = trivia.withLocation(alloc, SourceLocation(BufferID(1, "asdf"), 5));
    CHECK(trivia.getRawText() == "/**/");
    CHECK(trivia.getExplicitLocation()->offset() == 1);
}

TEST_CASE("Directive trivia location") {
    auto& text = "//bar\n`define FOO bar";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::EndOfFile);
    REQUIRE(token.trivia().size() == 1);

    Trivia t = token.trivia()[0];
    CHECK(t.kind == TriviaKind::Directive);
    REQUIRE(t.syntax()->kind == SyntaxKind::DefineDirective);
    CHECK(t.getExplicitLocation()->offset() == 0);

    CHECK_DIAGNOSTICS_EMPTY;
}

void testExpect(TokenKind kind) {
    diagnostics.clear();
    Token actual(alloc, TokenKind::Identifier, {}, "SDF", SourceLocation(BufferID(1, "asdf"), 5));
    Token token = Token::createExpected(alloc, diagnostics, actual, kind, Token(), Token());

    CHECK(token.kind == kind);
    CHECK(token.trivia().empty());
    CHECK(token.location().offset() == 5);
    CHECK(token.isMissing());

    if (!LF::isKeyword(kind)) {
        CHECK(token.valueText().empty());
        CHECK(token.rawText().empty());
    }
}

TEST_CASE("Missing / expected tokens") {
    testExpect(TokenKind::IncludeFileName);
    testExpect(TokenKind::StringLiteral);
    testExpect(TokenKind::IntegerLiteral);
    testExpect(TokenKind::TimeLiteral);
    testExpect(TokenKind::WithKeyword);
}

TEST_CASE("Hex escape corner case") {
    auto& text = R"("\x)";
    Token token = lexToken(text);

    CHECK(token.kind == TokenKind::StringLiteral);
    CHECK(token.toString() == text);
    REQUIRE(!diagnostics.empty());
    CHECK(diagnostics[0].code == diag::InvalidHexEscapeCode);
    CHECK(diagnostics[1].code == diag::ExpectedClosingQuote);
}

TEST_CASE("Compat translate_on/off pragmas") {
    LexerOptions options;
    options.commentHandlers["pragma"]["synthesis_off"] = {CommentHandler::TranslateOff,
                                                          "synthesis_on"};
    options.commentHandlers["synthesis"]["translate_off"] = {CommentHandler::TranslateOff,
                                                             "translate_on"};

    auto& sm = getSourceManager();
    auto buffer = sm.assignText(R"(
a
// pragma synthesis_off
b
// pragma synthesis_on
c
/* synthesis translate_off */
d
// synthesis translate_off
e
/* synthesis translate_on */
f
)"sv);

    diagnostics.clear();
    Lexer lexer(buffer, alloc, diagnostics, sm, options);

    for (auto& text : {"a"sv, "c"sv, "f"sv}) {
        Token tok = lexer.lex();
        REQUIRE(tok.kind == TokenKind::Identifier);
        CHECK(!tok.rawText().compare(text));
    }

    CHECK(lexer.lex().kind == TokenKind::EndOfFile);
    CHECK(diagnostics.empty());
}

TEST_CASE("Compat translate_on/off pragmas unclosed") {
    LexerOptions options;
    options.commentHandlers["pragma"]["synthesis_off"] = {CommentHandler::TranslateOff,
                                                          "synthesis_on"};
    options.commentHandlers["synthesis"]["translate_off"] = {CommentHandler::TranslateOff,
                                                             "translate_on"};

    auto& sm = getSourceManager();
    auto buffer = sm.assignText(R"(
a
// pragma synthesis_off
b
// pragma synthesis_on
c
// synthesis translate_off
d
e
f
)"sv);

    diagnostics.clear();
    Lexer lexer(buffer, alloc, diagnostics, sm, options);
    for (auto& text : {"a"sv, "c"sv}) {
        Token tok = lexer.lex();
        REQUIRE(tok.kind == TokenKind::Identifier);
        CHECK(!tok.rawText().compare(text));
    }

    CHECK(lexer.lex().kind == TokenKind::EndOfFile);

    REQUIRE(diagnostics.size() == 1);
    CHECK(diagnostics[0].code == diag::UnclosedTranslateOff);
}
