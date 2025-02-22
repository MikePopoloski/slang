//------------------------------------------------------------------------------
// Lexer.cpp
// Source file lexer
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/parsing/Lexer.h"

#include <cmath>
#include <fmt/core.h>

#include "slang/diagnostics/LexerDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/diagnostics/PreprocessorDiags.h"
#include "slang/syntax/SyntaxKind.h"
#include "slang/text/CharInfo.h"
#include "slang/text/SourceManager.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/ScopeGuard.h"
#include "slang/util/String.h"

static_assert(std::numeric_limits<double>::is_iec559, "SystemVerilog requires IEEE 754");

static const double BitsPerDecimal = log2(10.0);

namespace slang::parsing {

using namespace syntax;

using LF = LexerFacts;

Lexer::Lexer(SourceBuffer buffer, BumpAllocator& alloc, Diagnostics& diagnostics,
             SourceManager& sourceManager, LexerOptions options) :
    Lexer(buffer.id, buffer.data, buffer.data.data(), alloc, diagnostics, sourceManager,
          std::move(options)) {
    library = buffer.library;
}

Lexer::Lexer(BufferID bufferId, std::string_view source, const char* startPtr, BumpAllocator& alloc,
             Diagnostics& diagnostics, SourceManager& sourceManager, LexerOptions options) :
    alloc(alloc), diagnostics(diagnostics), options(std::move(options)), bufferId(bufferId),
    originalBegin(source.data()), sourceBuffer(startPtr),
    sourceEnd(source.data() + source.length()), marker(nullptr), sourceManager(sourceManager) {

    ptrdiff_t count = sourceEnd - sourceBuffer;
    SLANG_ASSERT(count);
    SLANG_ASSERT(sourceEnd[-1] == '\0');

    // detect BOMs so we can give nice errors for invalid encoding
    if (count >= 2) {
        const unsigned char* ubuf = reinterpret_cast<const unsigned char*>(sourceBuffer);
        if ((ubuf[0] == 0xFF && ubuf[1] == 0xFE) || (ubuf[0] == 0xFE && ubuf[1] == 0xFF)) {
            errorCount++;
            addDiag(diag::UnicodeBOM, 0);
            advance(2);
        }
        else if (count >= 3) {
            // Silently skip the UTF8 BOM.
            if (ubuf[0] == 0xEF && ubuf[1] == 0xBB && ubuf[2] == 0xBF)
                advance(3);
        }
    }
}

Token Lexer::concatenateTokens(BumpAllocator& alloc, SourceManager& sourceManager, Token left,
                               Token right) {
    auto location = left.location();
    auto trivia = left.trivia();

    // if either side is empty, we have an error; the user tried to concatenate some weird kind of
    // token
    auto leftText = left.rawText();
    auto rightText = right.rawText();
    if (leftText.empty() || rightText.empty())
        return Token();

    // combine the text for both sides; make sure to include room for a null
    size_t newLength = leftText.length() + rightText.length() + 1;
    char* mem = (char*)alloc.allocate(newLength, 1);
    leftText.copy(mem, leftText.length());
    rightText.copy(mem + leftText.length(), rightText.length());
    mem[newLength - 1] = '\0';
    std::string_view combined{mem, newLength};

    Diagnostics unused;
    Lexer lexer{BufferID::getPlaceholder(),
                combined,
                combined.data(),
                alloc,
                unused,
                sourceManager,
                LexerOptions{}};

    auto token = lexer.lex();
    if (token.kind == TokenKind::Unknown || token.rawText().empty())
        return Token();

    // make sure the next token is an EoF, otherwise the tokens were unable to
    // be combined and should be left alone
    if (lexer.lex().kind != TokenKind::EndOfFile)
        return Token();

    return token.clone(alloc, trivia, token.rawText(), location);
}

Token Lexer::stringify(Lexer& parentLexer, Token startToken, std::span<Token> bodyTokens,
                       Token endToken) {
    SmallVector<char> text;
    text.push_back('"');

    const bool tripleQuoted = startToken.kind == TokenKind::MacroTripleQuote;
    if (tripleQuoted) {
        text.push_back('"');
        text.push_back('"');
    }

    auto addTrivia = [&](Token cur) {
        for (const Trivia& t : cur.trivia()) {
            if (t.kind == TriviaKind::Whitespace ||
                (tripleQuoted && t.kind == TriviaKind::EndOfLine)) {
                text.append_range(t.getRawText());
            }
        }
    };

    for (auto cur : bodyTokens) {
        addTrivia(cur);

        if (cur.kind == TokenKind::MacroEscapedQuote) {
            text.push_back('\\');
            text.push_back('"');
        }
        else if (cur.kind == TokenKind::StringLiteral) {
            auto raw = cur.rawText();
            const bool nestedHasTriple = raw.starts_with("\"\"\""sv);
            if (nestedHasTriple) {
                text.append_range(R"(\"\"\")"sv);
                raw = raw.substr(3, raw.size() - 6);
            }
            else {
                text.append_range(R"(\")"sv);
                raw = raw.substr(1, raw.size() - 2);
            }

            text.append_range(raw);

            if (nestedHasTriple)
                text.append_range(R"(\"\"\")"sv);
            else
                text.append_range(R"(\")"sv);
        }
        else if (cur.kind != TokenKind::EmptyMacroArgument) {
            text.append_range(cur.rawText());
        }
    }

    if (endToken)
        addTrivia(endToken);

    if (tripleQuoted) {
        text.push_back('"');
        text.push_back('"');
    }

    text.push_back('"');
    text.push_back('\0');

    std::string_view raw = toStringView(text.copy(parentLexer.alloc));

    Diagnostics unused;
    Lexer lexer{BufferID::getPlaceholder(), raw,    raw.data(),
                parentLexer.alloc,          unused, parentLexer.sourceManager,
                parentLexer.options};

    auto token = lexer.lex();
    SLANG_ASSERT(token.kind == TokenKind::StringLiteral);
    SLANG_ASSERT(lexer.lex().kind == TokenKind::EndOfFile);

    return token.clone(parentLexer.alloc, startToken.trivia(), raw.substr(0, raw.length() - 1),
                       startToken.location());
}

Trivia Lexer::commentify(BumpAllocator& alloc, SourceManager& sourceManager,
                         std::span<Token> tokens) {
    SmallVector<char> text;
    for (auto cur : tokens) {
        for (const Trivia& t : cur.trivia())
            text.append_range(t.getRawText());

        if (cur.kind != TokenKind::EmptyMacroArgument)
            text.append_range(cur.rawText());
    }
    text.push_back('\0');

    std::string_view raw = toStringView(text.copy(alloc));

    Diagnostics unused;
    Lexer lexer{
        BufferID::getPlaceholder(), raw, raw.data(), alloc, unused, sourceManager, LexerOptions{}};

    auto token = lexer.lex();
    SLANG_ASSERT(token.kind == TokenKind::EndOfFile);
    SLANG_ASSERT(token.trivia().size() == 1);

    return token.trivia()[0];
}

void Lexer::splitTokens(BumpAllocator& alloc, Diagnostics& diagnostics,
                        SourceManager& sourceManager, Token sourceToken, size_t offset,
                        KeywordVersion keywordVersion, SmallVectorBase<Token>& results) {
    auto loc = sourceToken.location();
    if (sourceManager.isMacroLoc(loc))
        loc = sourceManager.getOriginalLoc(loc);

    auto sourceText = sourceManager.getSourceText(loc.buffer());
    SLANG_ASSERT(!sourceText.empty());

    Lexer lexer{loc.buffer(),  sourceText,  sourceToken.rawText().substr(offset).data(),
                alloc,         diagnostics, sourceManager,
                LexerOptions{}};

    size_t endOffset = loc.offset() + sourceToken.rawText().length();
    while (true) {
        Token token = lexer.lex(keywordVersion);
        if (token.kind == TokenKind::EndOfFile || token.location().buffer() != loc.buffer() ||
            token.location().offset() >= endOffset)
            break;

        results.push_back(token);
    }
}

Token Lexer::lex() {
    return lex(LF::getDefaultKeywordVersion(options.languageVersion));
}

Token Lexer::lex(KeywordVersion keywordVersion) {
    triviaBuffer.clear();
    lexTrivia<false>();

    // lex the next token
    mark();
    Token token = lexToken(keywordVersion);

    if (token.kind != TokenKind::EndOfFile && errorCount > options.maxErrors) {
        // Stop any further lexing by claiming to be at the end of the buffer.
        addDiag(diag::TooManyLexerErrors, currentOffset());
        sourceBuffer = sourceEnd - 1;

        triviaBuffer.push_back(Trivia(TriviaKind::DisabledText, lexeme()));
        return Token(alloc, TokenKind::EndOfFile, triviaBuffer.copy(alloc), token.rawText(),
                     token.location());
    }

    return token;
}

bool Lexer::isNextTokenOnSameLine() {
    auto guard = ScopeGuard([this, currBuff = sourceBuffer] { sourceBuffer = currBuff; });

    while (true) {
        switch (peek()) {
            case ' ':
            case '\t':
            case '\v':
            case '\f':
                advance();
                break;
            case '/':
                switch (peek(1)) {
                    case '/':
                        return false;
                    case '*':
                        advance(2);
                        while (true) {
                            if (consume('*') && consume('/'))
                                break;
                            if (peek() == '\0' && reallyAtEnd())
                                return false;
                            advance();
                        }
                        break;
                    default:
                        return true;
                }
                break;
            case '\0':
            case '\r':
            case '\n':
                return false;
            default:
                return true;
        }
    }
}

Token Lexer::lexEncodedText(ProtectEncoding encoding, uint32_t expectedBytes, bool singleLine,
                            bool legacyProtectedMode) {
    triviaBuffer.clear();
    lexTrivia<true>();
    mark();
    scanEncodedText(encoding, expectedBytes, singleLine, legacyProtectedMode);
    return create(TokenKind::Unknown);
}

Token Lexer::lexToken(KeywordVersion keywordVersion) {
    char c = peek();
    advance();
    switch (c) {
        case '\0':
            // check if we're not really at the end
            // we back up one character here so that if the user calls lex() again and again,
            // he'll just keep getting back EndOfFile tokens over and over
            sourceBuffer--;
            if (!reallyAtEnd()) {
                errorCount++;
                addDiag(diag::EmbeddedNull, currentOffset());
                advance();
                return create(TokenKind::Unknown);
            }

            // otherwise, end of file
            return create(TokenKind::EndOfFile);
        case '!':
            if (consume('=')) {
                switch (peek()) {
                    case '=':
                        advance();
                        return create(TokenKind::ExclamationDoubleEquals);
                    case '?':
                        advance();
                        return create(TokenKind::ExclamationEqualsQuestion);
                    default:
                        return create(TokenKind::ExclamationEquals);
                }
            }
            return create(TokenKind::Exclamation);
        case '"':
            return lexStringLiteral();
        case '#':
            switch (peek()) {
                case '#':
                    advance();
                    return create(TokenKind::DoubleHash);
                case '-':
                    if (peek(1) == '#') {
                        advance(2);
                        return create(TokenKind::HashMinusHash);
                    }
                    // #- isn't a token, so just return a hash
                    return create(TokenKind::Hash);
                case '=':
                    if (peek(1) == '#') {
                        advance(2);
                        return create(TokenKind::HashEqualsHash);
                    }
                    // #= isn't a token, so just return a hash
                    return create(TokenKind::Hash);
            }
            return create(TokenKind::Hash);
        case '$':
            return lexDollarSign();
        case '%':
            if (consume('='))
                return create(TokenKind::PercentEqual);
            return create(TokenKind::Percent);
        case '&':
            switch (peek()) {
                case '&':
                    advance();
                    if (consume('&'))
                        return create(TokenKind::TripleAnd);
                    else
                        return create(TokenKind::DoubleAnd);
                case '=':
                    advance();
                    return create(TokenKind::AndEqual);
            }
            return create(TokenKind::And);
        case '\'':
            if (consume('{'))
                return create(TokenKind::ApostropheOpenBrace);
            else
                return lexApostrophe();
        case '(':
            return create(TokenKind::OpenParenthesis);
        case ')':
            return create(TokenKind::CloseParenthesis);
        case '*':
            switch (peek()) {
                case '*':
                    advance();
                    return create(TokenKind::DoubleStar);
                case '=':
                    advance();
                    return create(TokenKind::StarEqual);
                case '>':
                    advance();
                    return create(TokenKind::StarArrow);
            }
            return create(TokenKind::Star);
        case '+':
            switch (peek()) {
                case '+':
                    advance();
                    return create(TokenKind::DoublePlus);
                case '=':
                    advance();
                    return create(TokenKind::PlusEqual);
                case ':':
                    advance();
                    return create(TokenKind::PlusColon);
                case '/':
                    if (peek(1) == '-') {
                        advance(2);
                        return create(TokenKind::PlusDivMinus);
                    }
                    break;
                case '%':
                    if (peek(1) == '-') {
                        advance(2);
                        return create(TokenKind::PlusModMinus);
                    }
                    break;
            }
            return create(TokenKind::Plus);
        case ',':
            return create(TokenKind::Comma);
        case '-':
            switch (peek()) {
                case '-':
                    advance();
                    return create(TokenKind::DoubleMinus);
                case '=':
                    advance();
                    return create(TokenKind::MinusEqual);
                case ':':
                    advance();
                    return create(TokenKind::MinusColon);
                case '>':
                    advance();
                    if (consume('>'))
                        return create(TokenKind::MinusDoubleArrow);
                    else
                        return create(TokenKind::MinusArrow);
            }
            return create(TokenKind::Minus);
        case '.':
            return create(TokenKind::Dot);
        case '/':
            if (consume('='))
                return create(TokenKind::SlashEqual);
            else
                return create(TokenKind::Slash);
        case '0':
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7':
        case '8':
        case '9':
            // back up so that lexNumericLiteral can look at this digit again
            sourceBuffer--;
            return lexNumericLiteral();
        case ':':
            switch (peek()) {
                case '=':
                    advance();
                    return create(TokenKind::ColonEquals);
                case '/':
                    switch (peek(1)) {
                        case '/':
                        case '*':
                            return create(TokenKind::Colon);
                    }
                    advance();
                    return create(TokenKind::ColonSlash);
                case ':':
                    advance();
                    return create(TokenKind::DoubleColon);
            }
            return create(TokenKind::Colon);
        case ';':
            return create(TokenKind::Semicolon);
        case '<':
            switch (peek()) {
                case '=':
                    advance();
                    return create(TokenKind::LessThanEquals);
                case '-':
                    if (peek(1) == '>') {
                        advance(2);
                        return create(TokenKind::LessThanMinusArrow);
                    }
                    return create(TokenKind::LessThan);
                case '<':
                    advance();
                    switch (peek()) {
                        case '<':
                            if (peek(1) == '=') {
                                advance(2);
                                return create(TokenKind::TripleLeftShiftEqual);
                            }
                            else {
                                advance();
                                return create(TokenKind::TripleLeftShift);
                            }
                        case '=':
                            advance();
                            return create(TokenKind::LeftShiftEqual);
                    }
                    return create(TokenKind::LeftShift);
            }
            return create(TokenKind::LessThan);
        case '=':
            switch (peek()) {
                case '=':
                    advance();
                    switch (peek()) {
                        case '=':
                            advance();
                            return create(TokenKind::TripleEquals);
                        case '?':
                            advance();
                            return create(TokenKind::DoubleEqualsQuestion);
                    }
                    return create(TokenKind::DoubleEquals);
                case '>':
                    advance();
                    return create(TokenKind::EqualsArrow);
            }
            return create(TokenKind::Equals);
        case '>':
            switch (peek()) {
                case '=':
                    advance();
                    return create(TokenKind::GreaterThanEquals);
                case '>':
                    advance();
                    switch (peek()) {
                        case '>':
                            if (peek(1) == '=') {
                                advance(2);
                                return create(TokenKind::TripleRightShiftEqual);
                            }
                            else {
                                advance();
                                return create(TokenKind::TripleRightShift);
                            }
                        case '=':
                            advance();
                            return create(TokenKind::RightShiftEqual);
                    }
                    return create(TokenKind::RightShift);
            }
            return create(TokenKind::GreaterThan);
        case '?':
            return create(TokenKind::Question);
        case '@':
            switch (peek()) {
                case '@':
                    advance();
                    return create(TokenKind::DoubleAt);
                default:
                    return create(TokenKind::At);
            }
            // clang-format off
        case 'A': case 'B': case 'C': case 'D':
        case 'E': case 'F': case 'G': case 'H':
        case 'I': case 'J': case 'L': case 'K':
        case 'M': case 'N': case 'O': case 'P':
        case 'Q': case 'R': case 'S': case 'T':
        case 'U': case 'V': case 'W': case 'X':
        case 'Y': case 'Z':
        case 'a': case 'b': case 'c': case 'd':
        case 'e': case 'f': case 'g': case 'h':
        case 'i': case 'j': case 'k': case 'l':
        case 'm': case 'n': case 'o': case 'p':
        case 'q': case 'r': case 's': case 't':
        case 'u': case 'v': case 'w': case 'x':
        case 'y': case 'z':
        case '_': {
            // clang-format on
            scanIdentifier();

            // might be a keyword
            auto table = LF::getKeywordTable(keywordVersion);
            SLANG_ASSERT(table);
            if (auto it = table->find(lexeme()); it != table->end())
                return create(it->second);

            return create(TokenKind::Identifier);
        }
        case '[':
            return create(TokenKind::OpenBracket);
        case '\\':
            return lexEscapeSequence(false);
        case ']':
            return create(TokenKind::CloseBracket);
        case '^':
            switch (peek()) {
                case '~':
                    advance();
                    return create(TokenKind::XorTilde);
                case '=':
                    advance();
                    return create(TokenKind::XorEqual);
            }
            return create(TokenKind::Xor);
        case '`':
            switch (peek()) {
                case '"':
                    advance();
                    if (peek() == '"' && peek(1) == '"') {
                        advance(2);
                        return create(TokenKind::MacroTripleQuote);
                    }
                    else {
                        return create(TokenKind::MacroQuote);
                    }
                case '`':
                    advance();
                    return create(TokenKind::MacroPaste);
                case '\\':
                    if (peek(1) == '`' && peek(2) == '"') {
                        advance(3);
                        return create(TokenKind::MacroEscapedQuote);
                    }
                    return lexDirective();
            }
            return lexDirective();
        case '{':
            return create(TokenKind::OpenBrace);
        case '|':
            switch (peek()) {
                case '|':
                    advance();
                    return create(TokenKind::DoubleOr);
                case '-':
                    if (peek(1) == '>') {
                        advance(2);
                        return create(TokenKind::OrMinusArrow);
                    }
                    return create(TokenKind::Or);
                case '=':
                    if (peek(1) == '>') {
                        advance(2);
                        return create(TokenKind::OrEqualsArrow);
                    }
                    else {
                        advance();
                        return create(TokenKind::OrEqual);
                    }
            }
            return create(TokenKind::Or);
        case '}':
            return create(TokenKind::CloseBrace);
        case '~':
            switch (peek()) {
                case '&':
                    advance();
                    return create(TokenKind::TildeAnd);
                case '|':
                    advance();
                    return create(TokenKind::TildeOr);
                case '^':
                    advance();
                    return create(TokenKind::TildeXor);
            }
            return create(TokenKind::Tilde);
        default:
            errorCount++;
            if (isASCII(c)) {
                addDiag(diag::NonPrintableChar, currentOffset() - 1);
            }
            else {
                sourceBuffer--;
                addDiag(diag::UTF8Char, currentOffset());

                bool sawUTF8Error = false;
                do {
                    sawUTF8Error |= !scanUTF8Char(sawUTF8Error);
                } while (!isASCII(peek()));
            }
            return create(TokenKind::Unknown);
    }
}

Token Lexer::lexStringLiteral() {
    bool tripleQuoted = false;
    if (peek() == '"' && peek(1) == '"') {
        // New in v1800-2023: triple quoted string literals
        if (options.languageVersion < LanguageVersion::v1800_2023) {
            addDiag(diag::WrongLanguageVersion, currentOffset() - 1)
                << toString(options.languageVersion);
        }
        tripleQuoted = true;
        advance(2);
    }

    stringBuffer.clear();
    bool sawUTF8Error = false;
    while (true) {
        size_t offset = currentOffset();
        char c = peek();

        if (c == '\\') {
            advance();
            c = peek();
            advance();

            uint32_t charCode;
            switch (c) {
                    // clang-format off
                case 'n': stringBuffer.push_back('\n'); break;
                case 't': stringBuffer.push_back('\t'); break;
                case '\\': stringBuffer.push_back('\\'); break;
                case '"': stringBuffer.push_back('"'); break;
                case 'v': stringBuffer.push_back('\v'); break;
                case 'f': stringBuffer.push_back('\f'); break;
                case 'a': stringBuffer.push_back('\a'); break;
                case '\n': break;
                case '\r': consume('\n'); break;
                case '0': case '1': case '2': case '3':
                case '4': case '5': case '6': case '7':
                    // clang-format on
                    // octal character code
                    charCode = getDigitValue(c);
                    if (isOctalDigit(c = peek())) {
                        advance();
                        charCode = (charCode * 8) + getDigitValue(c);
                        if (isOctalDigit(c = peek())) {
                            advance();
                            charCode = (charCode * 8) + getDigitValue(c);
                            if (charCode > 255) {
                                addDiag(diag::OctalEscapeCodeTooBig, offset);
                                break;
                            }
                        }
                    }
                    stringBuffer.push_back((char)charCode);
                    break;
                case 'x':
                    c = peek();
                    if (!isHexDigit(c)) {
                        addDiag(diag::InvalidHexEscapeCode, offset);
                        stringBuffer.push_back('x');
                    }
                    else {
                        advance();
                        charCode = getHexDigitValue(c);
                        if (isHexDigit(c = peek())) {
                            advance();
                            charCode = (charCode * 16) + getHexDigitValue(c);
                        }
                        stringBuffer.push_back((char)charCode);
                    }
                    break;
                default: {
                    auto curr = --sourceBuffer;

                    uint32_t unicodeChar;
                    int unicodeLen;
                    if (scanUTF8Char(sawUTF8Error, &unicodeChar, unicodeLen)) {
                        if (isPrintableUnicode(unicodeChar)) {
                            // '\%' is not an actual escape code but other tools silently allow it
                            // and major UVM headers use it, so we'll issue a (fairly quiet) warning
                            // about it. Otherwise issue a louder warning (on by default).
                            DiagCode code = c == '%' ? diag::NonstandardEscapeCode
                                                     : diag::UnknownEscapeCode;
                            addDiag(code, offset) << std::string_view(curr, (size_t)unicodeLen);
                        }
                    }
                    else {
                        sawUTF8Error = true;
                    }

                    // Back up so that we handle this character as a normal char in the outer loop,
                    // regardless of whether it's valid or not.
                    sourceBuffer = curr;
                    break;
                }
            }
        }
        else if (c == '"') {
            if (tripleQuoted) {
                if (peek(1) == '"' && peek(2) == '"') {
                    advance(3);
                    break;
                }
                else {
                    advance();
                    stringBuffer.push_back(c);
                    sawUTF8Error = false;
                }
            }
            else {
                advance();
                break;
            }
        }
        else if (isNewline(c) && !tripleQuoted) {
            addDiag(diag::ExpectedClosingQuote, offset);
            break;
        }
        else if (c == '\0') {
            if (reallyAtEnd()) {
                addDiag(diag::ExpectedClosingQuote, offset);
                break;
            }

            // otherwise just error and ignore
            errorCount++;
            addDiag(diag::EmbeddedNull, offset);
            advance();
        }
        else if (isASCII(c)) {
            advance();
            stringBuffer.push_back(c);
            sawUTF8Error = false;
        }
        else {
            auto curr = sourceBuffer;

            uint32_t unused;
            int unicodeLen;
            sawUTF8Error |= !scanUTF8Char(sawUTF8Error, &unused, unicodeLen);

            // Regardless of whether the character sequence was valid or not
            // we want to add the bytes to the string, to allow for cases where
            // the source is actually something like latin-1 encoded. Ignoring the
            // warning and carrying on will do the right thing for them.
            for (int i = 0; i < unicodeLen; i++)
                stringBuffer.push_back(curr[i]);
        }
    }

    return create(TokenKind::StringLiteral, toStringView(stringBuffer.copy(alloc)));
}

Token Lexer::lexEscapeSequence(bool isMacroName) {
    char c = peek();
    if (isWhitespace(c) || c == '\0') {
        // Check for a line continuation sequence.
        if (isNewline(c)) {
            advance();
            if (c == '\r' && peek() == '\n')
                advance();
            return create(TokenKind::LineContinuation);
        }

        // Error issued in the Preprocessor
        return create(TokenKind::Unknown);
    }

    while (isPrintableASCII(c)) {
        advance();
        c = peek();
        if (isWhitespace(c))
            break;
    }

    if (isMacroName)
        return create(TokenKind::Directive, SyntaxKind::MacroUsage);

    return create(TokenKind::Identifier);
}

Token Lexer::lexDollarSign() {
    scanIdentifier();

    // if length is 1, we just have a dollar sign operator
    if (lexemeLength() == 1)
        return create(TokenKind::Dollar);

    // otherwise, we have a system identifier
    // check for system keywords
    TokenKind kind = LF::getSystemKeywordKind(lexeme());
    if (kind != TokenKind::Unknown)
        return create(kind);

    return create(TokenKind::SystemIdentifier);
}

Token Lexer::lexDirective() {
    if (peek() == '\\') {
        // Handle escaped macro names as well.
        advance();
        return lexEscapeSequence(true);
    }

    scanIdentifier();

    // if length is 1, we just have a grave character on its own, which is an error
    if (lexemeLength() == 1) {
        // Error issued in the Preprocessor
        return create(TokenKind::Unknown);
    }

    SyntaxKind directive = LF::getDirectiveKind(lexeme().substr(1), options.enableLegacyProtect);
    return create(TokenKind::Directive, directive);
}

Token Lexer::lexNumericLiteral() {
    // have to check for the "1step" magic keyword
    static const char OneStepText[] = "1step";
    for (int i = 0; i < (int)sizeof(OneStepText) - 1; i++) {
        if (peek(i) != OneStepText[i])
            break;
        if (i == sizeof(OneStepText) - 2) {
            advance(sizeof(OneStepText) - 1);
            return create(TokenKind::OneStep);
        }
    }

    // scan past leading zeros
    while (peek() == '0')
        advance();

    // Keep track of digits as we iterate through them; convert them
    // into logic_t to pass into the SVInt parsing method. If it turns out
    // that this is actually a float, we'll go back and populate `floatChars`
    // instead. Since we expect many more ints than floats, it makes sense to
    // not waste time populating that array up front.
    size_t startOfNum = currentOffset();
    SmallVector<logic_t> digits;
    SmallVector<char> floatChars;

    while (true) {
        char c = peek();
        if (c == '_')
            advance();
        else if (!isDecimalDigit(c))
            break;
        else {
            digits.push_back(logic_t(getDigitValue(c)));
            advance();
        }
    }

    auto populateChars = [&]() {
        if (digits.empty())
            floatChars.push_back('0');
        else {
            for (auto d : digits)
                floatChars.push_back(char((char)d.value + '0'));
        }
    };

    // Check for fractional digits.
    if (peek() == '.') {
        advance();
        populateChars();
        floatChars.push_back('.');

        bool any = false;
        while (true) {
            char c = peek();
            if (c == '_')
                advance();
            else if (!isDecimalDigit(c))
                break;
            else {
                any = true;
                floatChars.push_back(c);
                advance();
            }
        }

        if (!any)
            floatChars.push_back('0');
    }

    // Check for an exponent. Note that this case can be indistinguishable from
    // the vector digits for a hex literal, so we can't issue any errors here if
    // we don't have a decimal point (from above).
    //
    // Consider this nasty case we need to support:
    // `FOO 3e+2
    // If `FOO is defined to be 'h this represents an expression: 62 + 2
    // Otherwise, this represents a real literal: 300.0

    std::optional<TimeUnit> timeSuffix;
    char c = peek();
    if (c == 'e' || c == 'E') {
        bool hasDecimal = !floatChars.empty();
        if (!hasDecimal)
            populateChars();

        floatChars.push_back('e');

        // skip over leading sign
        int index = 1;
        c = peek(index);
        if (c == '+' || c == '-') {
            floatChars.push_back(c);
            c = peek(++index);
        }

        bool any = false;
        while (true) {
            if (c == '_')
                c = peek(++index);
            else if (!isDecimalDigit(c))
                break;
            else {
                any = true;
                floatChars.push_back(c);
                c = peek(++index);
            }
        }

        if (any || hasDecimal) {
            advance(index);
            if (!any)
                floatChars.push_back('1');
        }
        else {
            // This isn't a float, it's probably a hex literal. Back up (by not calling advance)
            // and clear out the floatChars array so we don't think it should be a float.
            floatChars.clear();
        }
    }
    else {
        // Check for a time literal suffix directly adjacent. Time literal
        // values are always interpreted as doubles.
        timeSuffix = lexTimeLiteral();
        if (timeSuffix && floatChars.empty())
            populateChars();
    }

    if (!floatChars.empty()) {
        // We have a floating point result. Let the standard library do the heavy lifting of
        // converting and rounding correctly. Note that we depend on this code returning
        // 0 for underflow and +inf for overflow.
        floatChars.push_back('\0');

        char* end;
        errno = 0;
        double value = strtod(floatChars.data(), &end);
        SLANG_ASSERT(end == floatChars.end() - 1); // should never error

        // If we had an overflow or underflow, errno is now ERANGE. We can't warn here in case
        // this turns out to actually be a hex literal. Have the token carry this info so someone
        // can check it later if they care.
        bool outOfRange = errno == ERANGE;

        return create(timeSuffix ? TokenKind::TimeLiteral : TokenKind::RealLiteral, value,
                      outOfRange, timeSuffix);
    }

    // normal numeric literal
    SVInt intVal;
    if (!digits.empty()) {
        double bitsDbl = ceil(BitsPerDecimal * double(digits.size()));
        bitwidth_t bits;
        if (bitsDbl <= double(SVInt::MAX_BITS))
            bits = (bitwidth_t)bitsDbl;
        else {
            addDiag(diag::LiteralSizeTooLarge, startOfNum) << (int)SVInt::MAX_BITS;
            bits = SVInt::MAX_BITS;
        }

        intVal = SVInt::fromDigits(bits, LiteralBase::Decimal, false, false, digits);
        intVal.shrinkToFit();
    }

    return create(TokenKind::IntegerLiteral, intVal);
}

Token Lexer::lexApostrophe() {
    char c = peek();
    switch (c) {
        case '0':
        case '1':
            advance();
            return create(TokenKind::UnbasedUnsizedLiteral, (logic_t)getDigitValue(c));
        case 'x':
        case 'X':
            advance();
            return create(TokenKind::UnbasedUnsizedLiteral, logic_t::x);
        case 'Z':
        case 'z':
            advance();
            return create(TokenKind::UnbasedUnsizedLiteral, logic_t::z);
        case 's':
        case 'S': {
            advance();
            LiteralBase base;
            if (!literalBaseFromChar(peek(), base))
                base = LiteralBase::Decimal;
            else
                advance();
            return create(TokenKind::IntegerBase, base, true);
        }
        default: {
            LiteralBase base;
            if (literalBaseFromChar(peek(), base)) {
                advance();
                return create(TokenKind::IntegerBase, base, false);
            }

            // otherwise just an apostrophe token
            return create(TokenKind::Apostrophe);
        }
    }
}

std::optional<TimeUnit> Lexer::lexTimeLiteral() {
#define CASE(c, flag)              \
    case c:                        \
        if (peek(1) == 's') {      \
            advance(2);            \
            return TimeUnit::flag; \
        }                          \
        break;

    // clang-format off
    switch (peek()) {
        case 's':
            advance();
            return TimeUnit::Seconds;
        CASE('m', Milliseconds);
        CASE('u', Microseconds);
        CASE('n', Nanoseconds);
        CASE('p', Picoseconds);
        CASE('f', Femtoseconds);
        default:
            break;
    }
#undef CASE
    // clang-format on
    return std::nullopt;
}

template<bool StopAfterNewline>
void Lexer::lexTrivia() {
    while (true) {
        mark();

        switch (peek()) {
            case ' ':
            case '\t':
            case '\v':
            case '\f':
                advance();
                scanWhitespace();
                break;
            case '/':
                switch (peek(1)) {
                    case '/':
                        advance(2);
                        scanLineComment();
                        break;
                    case '*': {
                        advance(2);
                        scanBlockComment();
                        break;
                    }
                    default:
                        return;
                }
                break;
            case '\r':
                advance();
                consume('\n');
                addTrivia(TriviaKind::EndOfLine);
                if (StopAfterNewline)
                    return;
                break;
            case '\n':
                advance();
                addTrivia(TriviaKind::EndOfLine);
                if (StopAfterNewline)
                    return;
                break;
            default:
                return;
        }
    }
}

void Lexer::scanIdentifier() {
    while (true) {
        char c = peek();
        if (isAlphaNumeric(c) || c == '_' || c == '$')
            advance();
        else
            return;
    }
}

void Lexer::scanWhitespace() {
    bool done = false;
    while (!done) {
        switch (peek()) {
            case ' ':
            case '\t':
            case '\v':
            case '\f':
                advance();
                break;
            default:
                done = true;
                break;
        }
    }
    addTrivia(TriviaKind::Whitespace);
}

void Lexer::scanLineComment() {
    if (tryApplyCommentHandler()) [[unlikely]] {
        addTrivia(TriviaKind::DisabledText);
        return;
    }

    bool sawUTF8Error = false;
    while (true) {
        char c = peek();
        if (isASCII(c)) {
            if (isNewline(c))
                break;

            sawUTF8Error = false;
            if (c == '\0') {
                if (reallyAtEnd())
                    break;

                // otherwise just error and ignore
                errorCount++;
                addDiag(diag::EmbeddedNull, currentOffset());
            }
            advance();
        }
        else {
            sawUTF8Error |= !scanUTF8Char(sawUTF8Error);
        }
    }

    addTrivia(TriviaKind::LineComment);
}

void Lexer::scanBlockComment() {
    if (tryApplyCommentHandler()) [[unlikely]] {
        addTrivia(TriviaKind::DisabledText);
        return;
    }

    bool sawUTF8Error = false;
    while (true) {
        char c = peek();
        if (isASCII(c)) {
            sawUTF8Error = false;
            if (c == '*' && peek(1) == '/') {
                advance(2);
                break;
            }
            else if (c == '/' && peek(1) == '*') {
                // nested block comments disallowed by the standard; ignore and continue
                addDiag(diag::NestedBlockComment, currentOffset());
                advance(2);
            }
            else if (c == '\0') {
                if (reallyAtEnd()) {
                    addDiag(diag::UnterminatedBlockComment, currentOffset());
                    break;
                }

                // otherwise just error and ignore
                errorCount++;
                addDiag(diag::EmbeddedNull, currentOffset());
                advance();
            }
            else {
                advance();
            }
        }
        else {
            sawUTF8Error |= !scanUTF8Char(sawUTF8Error);
        }
    }

    addTrivia(TriviaKind::BlockComment);
}

bool Lexer::tryApplyCommentHandler() {
    auto nextWord = [&]() {
        // Skip over leading spaces and tabs.
        while (isTabOrSpace(peek()))
            advance();

        auto start = sourceBuffer;
        while (true) {
            char c = peek();
            if (!isAlphaNumeric(c) && c != '_' && c != '-')
                break;

            advance();
        }

        return std::string_view(start, size_t(sourceBuffer - start));
    };

    auto firstWord = nextWord();
    auto it = options.commentHandlers.find(firstWord);
    if (it == options.commentHandlers.end()) [[likely]]
        return false;

    auto it2 = it->second.find(nextWord());
    if (it2 == it->second.end())
        return false;

    auto loc = [&] { return SourceLocation(bufferId, currentOffset()); };

    auto& handler = it2->second;
    switch (handler.kind) {
        case CommentHandler::Protect:
            // We need to see begin_protected, otherwise we ignore.
            if (nextWord() == "begin_protected"sv) {
                addDiag(diag::ProtectedEnvelope, currentOffset() - lexemeLength());
                scanDisabledRegion(firstWord, "protect", "end_protected", diag::RawProtectEOF);
                return true;
            }
            return false;
        case CommentHandler::TranslateOff:
            scanDisabledRegion(firstWord, handler.endRegion, std::nullopt,
                               diag::UnclosedTranslateOff);
            return true;
        case CommentHandler::LintOff:
            sourceManager.addDiagnosticDirective(loc(), nextWord(), DiagnosticSeverity::Ignored);
            return false;
        case CommentHandler::LintOn:
            sourceManager.addDiagnosticDirective(loc(), nextWord(), DiagnosticSeverity::Warning);
            return false;
        case CommentHandler::LintSave:
            sourceManager.addDiagnosticDirective(loc(), "__push__", DiagnosticSeverity::Ignored);
            return false;
        case CommentHandler::LintRestore:
            sourceManager.addDiagnosticDirective(loc(), "__pop__", DiagnosticSeverity::Ignored);
            return false;
        default:
            SLANG_UNREACHABLE;
    }
}

bool Lexer::scanUTF8Char(bool alreadyErrored) {
    uint32_t unused1;
    int unused2;
    return scanUTF8Char(alreadyErrored, &unused1, unused2);
}

bool Lexer::scanUTF8Char(bool alreadyErrored, uint32_t* code, int& computedLen) {
    int error;
    auto curr = sourceBuffer;
    if (sourceBuffer + 4 < sourceEnd) {
        sourceBuffer = utf8Decode(sourceBuffer, code, &error, computedLen);
    }
    else {
        char buf[4] = {};
        auto spaceLeft = sourceEnd - sourceBuffer - 1;
        memcpy(buf, sourceBuffer, size_t(spaceLeft));

        auto next = utf8Decode(buf, code, &error, computedLen);
        sourceBuffer += std::min(next - buf, spaceLeft);
        computedLen = std::min(computedLen, (int)spaceLeft);
    }

    if (error) {
        // if error, trim next pointer so that control char is read as next char
        if ((computedLen > 1) && (curr[1] < 0x20))
            sourceBuffer = curr + 1;
        else if ((computedLen > 2) && (curr[2] < 0x20))
            sourceBuffer = curr + 2;
        else if ((computedLen > 3) && (curr[3] < 0x20))
            sourceBuffer = curr + 3;

        if (!alreadyErrored)
            addDiag(diag::InvalidUTF8Seq, (size_t)(curr - originalBegin));
        return false;
    }

    return true;
}

void Lexer::scanEncodedText(ProtectEncoding encoding, uint32_t expectedBytes, bool singleLine,
                            bool legacyProtectedMode) {
    // Helper function that returns true if the current position in the buffer
    // is looking at the string "pragma".
    auto lookingAtPragma = [&] {
        int index = 0;
        auto endStr = legacyProtectedMode ? "endprotected"sv : "pragma"sv;
        for (char c : endStr) {
            if (peek(++index) != c)
                return false;
        }
        return true;
    };

    auto invalidByte = [&](char invalidChar, std::string_view name) {
        auto& diag = addDiag(diag::InvalidEncodingByte, currentOffset()) << name;
        diag << (isPrintableASCII(invalidChar) ? std::string(1, invalidChar)
                                               : fmt::format("{:#04x}", invalidChar));

        // Try to skip ahead to the next `pragma directive to get us out of this region.
        while (true) {
            char c = peek();
            if (c == '\0' && reallyAtEnd())
                break;

            if (c == '`' && lookingAtPragma())
                break;

            if (singleLine && (c == '\r' || c == '\n'))
                break;

            advance();
        }
    };

    uint32_t byteCount = 0;
    while (true) {
        if (expectedBytes && byteCount >= expectedBytes && !singleLine) {
            if (byteCount != expectedBytes) {
                addDiag(diag::ProtectEncodingBytes, currentOffset() - 1)
                    << byteCount << expectedBytes;
            }
            return;
        }

        char c = peek();
        if (c == '\r' || c == '\n') {
            // If this is a single line region then we're done here.
            if (singleLine) {
                if (expectedBytes && byteCount != expectedBytes) {
                    addDiag(diag::ProtectEncodingBytes, currentOffset() - 1)
                        << byteCount << expectedBytes;
                }
                return;
            }

            // Otherwise continue on. This newline doesn't count toward our expected byte limit,
            // unless this is the quoted printable encoding.
            advance();
            if (c == '\r' && peek() == '\n')
                advance();

            if (encoding == ProtectEncoding::QuotedPrintable) {
                byteCount++;
                if (c == '\r' && peek(-1) == '\n')
                    byteCount++;
            }

            continue;
        }

        if (!expectedBytes && !singleLine && c == '`') {
            // Encoding tools probably shouldn't do this but if they do we
            // should try to gracefully guess the end of the region by looking
            // for another non-encoded pragma that ends it.
            if (lookingAtPragma())
                return;
        }

        switch (encoding) {
            case ProtectEncoding::UUEncode: {
                // uuencode tells us the length of the line up front, so use that
                // to read the whole line in one go. The encoding is invalid if that
                // doesn't match up with what we find in the data.
                if (c == '`') {
                    // The grave character is a special case meaning 0 characters on this line.
                    advance();
                    continue;
                }

                if (c < 0x20 || c > 0x20 + 45) {
                    invalidByte(c, "uuencode"sv);
                    return;
                }

                uint32_t count = uint32_t(c - 0x20);
                byteCount += count;
                advance();

                uint32_t encodedCount = (uint32_t)ceil(count * 4 / 3.0);
                for (uint32_t i = 0; i < encodedCount; i++) {
                    c = peek();
                    if (c < 0x20 || c > 0x60) {
                        invalidByte(c, "uuencode"sv);
                        return;
                    }
                    advance();
                }
                break;
            }
            case ProtectEncoding::Base64:
                byteCount += 3;
                for (int i = 0; i < 4; i++) {
                    c = peek();
                    if (i > 1 && c == '=') {
                        byteCount--;
                    }
                    else if (!isBase64Char(c)) {
                        invalidByte(c, "base64"sv);
                        return;
                    }

                    advance();
                }
                break;
            case ProtectEncoding::QuotedPrintable:
                if (!isPrintableASCII(c) && c != '\t') {
                    invalidByte(c, "quoted-printable"sv);
                    return;
                }

                advance();
                if (c == '=') {
                    // If this is a soft line break then it doesn't count
                    // towards our byte count. Otherwise this is an escaped
                    // character that does count.
                    c = peek();
                    if (c == '\r' || c == '\n') {
                        advance();
                        if (c == '\r' && peek() == '\n')
                            advance();
                        continue;
                    }

                    if (!isHexDigit(c) || !isHexDigit(peek(1))) {
                        invalidByte(c, "quoted-printable"sv);
                        return;
                    }

                    advance(2);
                }
                byteCount++;
                break;
            case ProtectEncoding::Raw:
                if (c == '\0' && reallyAtEnd()) {
                    addDiag(diag::RawProtectEOF, currentOffset() - 1);
                    return;
                }

                advance();
                byteCount++;
                break;
            default:
                SLANG_UNREACHABLE;
        }
    }
}

void Lexer::scanDisabledRegion(std::string_view firstWord, std::string_view secondWord,
                               std::optional<std::string_view> thirdWord, DiagCode unclosedDiag) {
    auto matchWord = [&](std::string_view word) {
        while (isTabOrSpace(peek()))
            advance();

        for (char c : word) {
            if (!consume(c))
                return false;
        }

        char c = peek();
        return isWhitespace(c) || c == '\0';
    };

    while (true) {
        char c = peek();
        if (c == '\0' && reallyAtEnd()) {
            auto& diag = addDiag(unclosedDiag, currentOffset() - lexemeLength());
            if (unclosedDiag == diag::UnclosedTranslateOff)
                diag << secondWord;
            return;
        }

        advance();
        if (c == '/' && (peek() == '/' || peek() == '*')) {
            const bool isBlockComment = peek() == '*';
            advance();

            if (matchWord(firstWord) && matchWord(secondWord)) {
                if (!thirdWord || matchWord(*thirdWord)) {
                    // Scan the rest of the comment and then return.
                    // We discard the comment trivia from the buffer
                    // so that this part of the region ends up as
                    // a DisabledText trivia instead.
                    if (isBlockComment)
                        scanBlockComment();
                    else
                        scanLineComment();
                    triviaBuffer.pop_back();
                    return;
                }
            }
        }
    }
}

template<typename... Args>
Token Lexer::create(TokenKind kind, Args&&... args) {
    SourceLocation location(bufferId, size_t(marker - originalBegin));
    return Token(alloc, kind, triviaBuffer.copy(alloc), lexeme(), location,
                 std::forward<Args>(args)...);
}

void Lexer::addTrivia(TriviaKind kind) {
    triviaBuffer.emplace_back(kind, lexeme());
}

Diagnostic& Lexer::addDiag(DiagCode code, size_t offset) {
    return diagnostics.add(code, SourceLocation(bufferId, offset));
}

size_t Lexer::currentOffset() const {
    return (size_t)(sourceBuffer - originalBegin);
}

} // namespace slang::parsing
