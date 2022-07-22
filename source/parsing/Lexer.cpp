//------------------------------------------------------------------------------
// Lexer.cpp
// Source file lexer
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/parsing/Lexer.h"

#include "../text/CharInfo.h"
#include <algorithm>
#include <cmath>

#include "slang/diagnostics/LexerDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/text/SourceManager.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/String.h"

static_assert(std::numeric_limits<double>::is_iec559, "SystemVerilog requires IEEE 754");

namespace slang {

using LF = LexerFacts;

Lexer::Lexer(SourceBuffer buffer, BumpAllocator& alloc, Diagnostics& diagnostics,
             LexerOptions options) :
    Lexer(buffer.id, buffer.data, buffer.data.data(), alloc, diagnostics, options) {
}

Lexer::Lexer(BufferID bufferId, string_view source, const char* startPtr, BumpAllocator& alloc,
             Diagnostics& diagnostics, LexerOptions options) :
    alloc(alloc),
    diagnostics(diagnostics), options(options), bufferId(bufferId), originalBegin(source.data()),
    sourceBuffer(startPtr), sourceEnd(source.data() + source.length()), marker(nullptr) {
    ptrdiff_t count = sourceEnd - sourceBuffer;
    ASSERT(count);
    ASSERT(sourceEnd[-1] == '\0');

    // detect BOMs so we can give nice errors for invaild encoding
    if (count >= 2) {
        const unsigned char* ubuf = reinterpret_cast<const unsigned char*>(sourceBuffer);
        if ((ubuf[0] == 0xFF && ubuf[1] == 0xFE) || (ubuf[0] == 0xFE && ubuf[1] == 0xFF)) {
            errorCount++;
            addDiag(diag::UnicodeBOM, 0);
            advance(2);
        }
        else if (count >= 3) {
            if (ubuf[0] == 0xEF && ubuf[1] == 0xBB && ubuf[2] == 0xBF) {
                errorCount++;
                addDiag(diag::UnicodeBOM, 0);
                advance(3);
            }
        }
    }
}

Token Lexer::concatenateTokens(BumpAllocator& alloc, Token left, Token right) {
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
    string_view combined{ mem, newLength };

    Diagnostics unused;
    Lexer lexer{
        BufferID::getPlaceholder(), combined, combined.data(), alloc, unused, LexerOptions{}
    };

    auto token = lexer.lex();
    if (token.kind == TokenKind::Unknown || token.rawText().empty())
        return Token();

    // make sure the next token is an EoF, otherwise the tokens were unable to
    // be combined and should be left alone
    if (lexer.lex().kind != TokenKind::EndOfFile)
        return Token();

    return token.clone(alloc, trivia, token.rawText(), location);
}

Token Lexer::stringify(BumpAllocator& alloc, SourceLocation location, span<Trivia const> trivia,
                       Token* begin, Token* end) {
    SmallVectorSized<char, 64> text;
    text.append('"');

    while (begin != end) {
        Token cur = *begin;

        for (const Trivia& t : cur.trivia()) {
            if (t.kind == TriviaKind::Whitespace)
                text.appendRange(t.getRawText());
        }

        if (cur.kind == TokenKind::MacroEscapedQuote) {
            text.append('\\');
            text.append('"');
        }
        else if (cur.kind == TokenKind::StringLiteral) {
            text.append('\\');
            text.append('"');

            auto raw = cur.rawText();
            if (raw.size() > 2)
                text.appendRange(raw.substr(1, raw.size() - 2));

            text.append('\\');
            text.append('"');
        }
        else if (cur.kind != TokenKind::EmptyMacroArgument) {
            text.appendRange(cur.rawText());
        }
        begin++;
    }
    text.append('"');
    text.append('\0');

    string_view raw = toStringView(text.copy(alloc));

    Diagnostics unused;
    Lexer lexer{ BufferID::getPlaceholder(), raw, raw.data(), alloc, unused, LexerOptions{} };

    auto token = lexer.lex();
    ASSERT(token.kind == TokenKind::StringLiteral);
    ASSERT(lexer.lex().kind == TokenKind::EndOfFile);

    return token.clone(alloc, trivia, raw.substr(0, raw.length() - 1), location);
}

Trivia Lexer::commentify(BumpAllocator& alloc, Token* begin, Token* end) {
    SmallVectorSized<char, 64> text;
    while (begin != end) {
        Token cur = *begin;
        for (const Trivia& t : cur.trivia())
            text.appendRange(t.getRawText());

        if (cur.kind != TokenKind::EmptyMacroArgument)
            text.appendRange(cur.rawText());

        begin++;
    }
    text.append('\0');

    string_view raw = toStringView(text.copy(alloc));

    Diagnostics unused;
    Lexer lexer{ BufferID::getPlaceholder(), raw, raw.data(), alloc, unused, LexerOptions{} };

    auto token = lexer.lex();
    ASSERT(token.kind == TokenKind::EndOfFile);
    ASSERT(token.trivia().size() == 1);

    return token.trivia()[0];
}

void Lexer::splitTokens(BumpAllocator& alloc, Diagnostics& diagnostics,
                        const SourceManager& sourceManager, Token sourceToken, size_t offset,
                        KeywordVersion keywordVersion, SmallVector<Token>& results) {
    auto loc = sourceToken.location();
    if (sourceManager.isMacroLoc(loc))
        loc = sourceManager.getOriginalLoc(loc);

    auto sourceText = sourceManager.getSourceText(loc.buffer());
    ASSERT(!sourceText.empty());

    Lexer lexer{ loc.buffer(), sourceText,  sourceToken.rawText().substr(offset).data(),
                 alloc,        diagnostics, LexerOptions{} };

    size_t endOffset = loc.offset() + sourceToken.rawText().length();
    while (true) {
        Token token = lexer.lex(keywordVersion);
        if (token.kind == TokenKind::EndOfFile || token.location().buffer() != loc.buffer() ||
            token.location().offset() >= endOffset)
            break;

        results.append(token);
    }
}

Token Lexer::lex(KeywordVersion keywordVersion) {
    triviaBuffer.clear();
    lexTrivia();

    // lex the next token
    mark();
    Token token = lexToken(keywordVersion);

    if (token.kind != TokenKind::EndOfFile && errorCount > options.maxErrors) {
        // Stop any further lexing by claiming to be at the end of the buffer.
        addDiag(diag::TooManyLexerErrors, currentOffset());
        sourceBuffer = sourceEnd - 1;

        triviaBuffer.append(Trivia(TriviaKind::DisabledText, lexeme()));
        return Token(alloc, TokenKind::EndOfFile, triviaBuffer.copy(alloc), token.rawText(),
                     token.location());
    }

    return token;
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
            if (!consume('*'))
                return create(TokenKind::OpenParenthesis);
            else
                return create(TokenKind::OpenParenthesisStar);
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
                case ')':
                    advance();
                    return create(TokenKind::StarCloseParenthesis);
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
            if (consume('*'))
                return create(TokenKind::DotStar);
            else
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
            TokenKind kind;
            if (LF::getKeywordTable(keywordVersion)->lookup(lexeme(), kind))
                return create(kind);

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
                    return create(TokenKind::MacroQuote);
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
            if (isASCII(c))
                addDiag(diag::NonPrintableChar, currentOffset() - 1);
            else {
                addDiag(diag::UTF8Char, currentOffset() - 1);

                // skip over UTF-8 sequences
                int skip = utf8SeqBytes(c);
                advance(std::min((int)(sourceEnd - sourceBuffer - 1), skip));
            }
            return create(TokenKind::Unknown);
    }
}

Token Lexer::lexStringLiteral() {
    SmallVectorSized<char, 128> stringBuffer;
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
                case 'n': stringBuffer.append('\n'); break;
                case 't': stringBuffer.append('\t'); break;
                case '\\': stringBuffer.append('\\'); break;
                case '"': stringBuffer.append('"'); break;
                case 'v': stringBuffer.append('\v'); break;
                case 'f': stringBuffer.append('\f'); break;
                case 'a': stringBuffer.append('\a'); break;
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
                    stringBuffer.append((char)charCode);
                    break;
                case 'x':
                    c = peek();
                    advance();
                    if (!isHexDigit(c)) {
                        addDiag(diag::InvalidHexEscapeCode, offset);
                        stringBuffer.append(c);
                    }
                    else {
                        charCode = getHexDigitValue(c);
                        if (isHexDigit(c = peek())) {
                            advance();
                            charCode = (charCode * 16) + getHexDigitValue(c);
                        }
                        stringBuffer.append((char)charCode);
                    }
                    break;
                default: {
                    // '\%' is not an actual escape code but other tools silently allow it
                    // and major UVM headers use it, so we'll issue a (fairly quiet) warning about
                    // it. Otherwise issue a louder warning (on by default).
                    DiagCode code =
                        c == '%' ? diag::NonstandardEscapeCode : diag::UnknownEscapeCode;
                    addDiag(code, offset) << c;
                    stringBuffer.append(c);
                    break;
                }
            }
        }
        else if (c == '"') {
            advance();
            break;
        }
        else if (isNewline(c)) {
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
        else {
            advance();
            stringBuffer.append(c);
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

        addDiag(diag::EscapedWhitespace, currentOffset());
        return create(TokenKind::Unknown);
    }

    while (isPrintable(c)) {
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

    // store the offset before scanning in order to easily report error locations
    size_t startingOffset = currentOffset();
    scanIdentifier();

    // if length is 1, we just have a grave character on its own, which is an error
    if (lexemeLength() == 1) {
        addDiag(diag::MisplacedDirectiveChar, startingOffset);
        return create(TokenKind::Unknown);
    }

    SyntaxKind directive = LF::getDirectiveKind(lexeme().substr(1));
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
    SmallVectorSized<logic_t, 32> digits;
    SmallVectorSized<char, 32> floatChars;

    while (true) {
        char c = peek();
        if (c == '_')
            advance();
        else if (!isDecimalDigit(c))
            break;
        else {
            digits.append(logic_t(getDigitValue(c)));
            advance();
        }
    }

    auto populateChars = [&]() {
        if (digits.empty())
            floatChars.append('0');
        else {
            for (auto d : digits)
                floatChars.append(char((char)d.value + '0'));
        }
    };

    // Check for fractional digits.
    if (peek() == '.') {
        advance();
        populateChars();
        floatChars.append('.');

        if (peek() == '_')
            addDiag(diag::DigitsLeadingUnderscore, currentOffset());

        bool any = false;
        while (true) {
            char c = peek();
            if (c == '_')
                advance();
            else if (!isDecimalDigit(c))
                break;
            else {
                any = true;
                floatChars.append(c);
                advance();
            }
        }

        if (!any) {
            addDiag(diag::MissingFractionalDigits, currentOffset());
            floatChars.append('0');
        }
    }

    // Check for an exponent. Note that this case can be indistinguishable from
    // the vector digits for a hex literal, so we can't issue any errors here if
    // we don't have a decimal point (from above).
    //
    // Consider this nasty case we need to support:
    // `FOO 3e+2
    // If `FOO is defined to be 'h this represents an expression: 62 + 2
    // Otherwise, this represents a real literal: 300.0

    optional<TimeUnit> timeSuffix;
    char c = peek();
    if (c == 'e' || c == 'E') {
        bool hasDecimal = !floatChars.empty();
        if (!hasDecimal)
            populateChars();

        floatChars.append('e');

        // skip over leading sign
        int index = 1;
        c = peek(index);
        if (c == '+' || c == '-') {
            floatChars.append(c);
            c = peek(++index);
        }

        if (c == '_' && hasDecimal)
            addDiag(diag::DigitsLeadingUnderscore, currentOffset());

        bool any = false;
        while (true) {
            if (c == '_')
                c = peek(++index);
            else if (!isDecimalDigit(c))
                break;
            else {
                any = true;
                floatChars.append(c);
                c = peek(++index);
            }
        }

        if (any || hasDecimal) {
            advance(index);
            if (!any) {
                addDiag(diag::MissingExponentDigits, currentOffset());
                floatChars.append('1');
            }
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
        floatChars.append('\0');

        char* end;
        errno = 0;
        double value = strtod(floatChars.data(), &end);
        ASSERT(end == floatChars.end() - 1); // should never error

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
        static const double BitsPerDecimal = log2(10.0);

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
        case '?':
            advance();
            return create(TokenKind::UnbasedUnsizedLiteral, logic_t::z);
        case 's':
        case 'S': {
            advance();
            LiteralBase base;
            if (!literalBaseFromChar(peek(), base)) {
                addDiag(diag::ExpectedIntegerBaseAfterSigned, currentOffset());
                base = LiteralBase::Decimal;
            }
            else {
                advance();
            }
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

optional<TimeUnit> Lexer::lexTimeLiteral() {
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
                break;
            case '\n':
                advance();
                addTrivia(TriviaKind::EndOfLine);
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
    while (true) {
        char c = peek();
        if (isNewline(c))
            break;

        if (c == '\0') {
            if (reallyAtEnd())
                break;

            // otherwise just error and ignore
            errorCount++;
            addDiag(diag::EmbeddedNull, currentOffset());
        }
        advance();
    }
    addTrivia(TriviaKind::LineComment);
}

void Lexer::scanBlockComment() {
    while (true) {
        char c = peek();
        if (c == '\0') {
            if (reallyAtEnd()) {
                addDiag(diag::UnterminatedBlockComment, currentOffset());
                break;
            }

            // otherwise just error and ignore
            errorCount++;
            addDiag(diag::EmbeddedNull, currentOffset());
            advance();
        }
        else if (c == '*' && peek(1) == '/') {
            advance(2);
            break;
        }
        else if (c == '/' && peek(1) == '*') {
            // nested block comments disallowed by the standard; ignore and continue
            addDiag(diag::NestedBlockComment, currentOffset());
            advance(2);
        }
        else {
            advance();
        }
    }

    addTrivia(TriviaKind::BlockComment);
}

template<typename... Args>
Token Lexer::create(TokenKind kind, Args&&... args) {
    SourceLocation location(bufferId, size_t(marker - originalBegin));
    return Token(alloc, kind, triviaBuffer.copy(alloc), lexeme(), location,
                 std::forward<Args>(args)...);
}

void Lexer::addTrivia(TriviaKind kind) {
    triviaBuffer.emplace(kind, lexeme());
}

Diagnostic& Lexer::addDiag(DiagCode code, size_t offset) {
    return diagnostics.add(code, SourceLocation(bufferId, offset));
}

size_t Lexer::currentOffset() {
    return (size_t)(sourceBuffer - originalBegin);
}

} // namespace slang
