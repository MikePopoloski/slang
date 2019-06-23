//------------------------------------------------------------------------------
// Lexer.cpp
// Source file lexer.
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

static_assert(std::numeric_limits<double>::is_iec559, "SystemVerilog requires IEEE 754");

namespace slang {

SyntaxKind getDirectiveKind(string_view directive);

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
            addDiag(diag::UnicodeBOM, 0);
            advance(2);
        }
        else if (count >= 3) {
            if (ubuf[0] == 0xEF && ubuf[1] == 0xBB && ubuf[2] == 0xBF) {
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
    uint32_t newLength = (uint32_t)(leftText.length() + rightText.length() + 1);
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

    auto info = alloc.emplace<Token::Info>(*token.getInfo());
    info->location = location;
    info->trivia = trivia;
    return Token(token.kind, info);
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
        else if (cur.kind != TokenKind::EmptyMacroArgument) {
            text.appendRange(cur.rawText());
        }
        begin++;
    }
    text.append('"');
    text.append('\0');

    string_view raw = to_string_view(text.copy(alloc));

    Diagnostics unused;
    Lexer lexer{ BufferID(), raw, raw.data(), alloc, unused, LexerOptions{} };

    auto token = lexer.lex();
    ASSERT(token.kind == TokenKind::StringLiteral);
    ASSERT(lexer.lex().kind == TokenKind::EndOfFile);

    auto info = alloc.emplace<Token::Info>(*token.getInfo());
    info->location = location;
    info->trivia = trivia;
    info->rawText = raw.substr(0, raw.length() - 1);
    return Token(token.kind, info);
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
            token.location().offset() > endOffset)
            break;

        results.append(token);
    }
}

Token Lexer::lex(KeywordVersion keywordVersion) {
    auto info = alloc.emplace<Token::Info>();
    SmallVectorSized<Trivia, 32> triviaBuffer;
    lexTrivia(triviaBuffer);

    // lex the next token
    mark();
    TokenKind kind = lexToken(info, keywordVersion);
    onNewLine = false;
    info->rawText = lexeme();

    if (kind != TokenKind::EndOfFile && diagnostics.size() > options.maxErrors) {
        // Stop any further lexing by claiming to be at the end of the buffer.
        // TODO: this check needs work
        addDiag(diag::TooManyLexerErrors, currentOffset());
        sourceBuffer = sourceEnd - 1;
        triviaBuffer.append(Trivia(TriviaKind::DisabledText, lexeme()));
        kind = TokenKind::EndOfFile;
    }
    info->trivia = triviaBuffer.copy(alloc);
    return Token(kind, info);
}

TokenKind Lexer::lexToken(Token::Info* info, KeywordVersion keywordVersion) {
    uint32_t offset = currentOffset();
    info->location = SourceLocation(bufferId, offset);

    char c = peek();
    advance();
    switch (c) {
        case '\0':
            // check if we're not really at the end
            // we back up one character here so that if the user calls lex() again and again,
            // he'll just keep getting back EndOfFile tokens over and over
            sourceBuffer--;
            if (!reallyAtEnd()) {
                advance();
                addDiag(diag::EmbeddedNull, offset);
                return TokenKind::Unknown;
            }

            // otherwise, end of file
            return TokenKind::EndOfFile;
        case '!':
            if (consume('=')) {
                switch (peek()) {
                    case '=':
                        advance();
                        return TokenKind::ExclamationDoubleEquals;
                    case '?':
                        advance();
                        return TokenKind::ExclamationEqualsQuestion;
                    default:
                        return TokenKind::ExclamationEquals;
                }
            }
            return TokenKind::Exclamation;
        case '"':
            lexStringLiteral(info);
            return TokenKind::StringLiteral;
        case '#':
            switch (peek()) {
                case '#':
                    advance();
                    return TokenKind::DoubleHash;
                case '-':
                    if (peek(1) == '#') {
                        advance(2);
                        return TokenKind::HashMinusHash;
                    }
                    // #- isn't a token, so just return a hash
                    return TokenKind::Hash;
                case '=':
                    if (peek(1) == '#') {
                        advance(2);
                        return TokenKind::HashEqualsHash;
                    }
                    // #= isn't a token, so just return a hash
                    return TokenKind::Hash;
            }
            return TokenKind::Hash;
        case '$':
            return lexDollarSign(info);
        case '%':
            if (consume('='))
                return TokenKind::PercentEqual;
            return TokenKind::Percent;
        case '&':
            switch (peek()) {
                case '&':
                    advance();
                    if (consume('&'))
                        return TokenKind::TripleAnd;
                    else
                        return TokenKind::DoubleAnd;
                case '=':
                    advance();
                    return TokenKind::AndEqual;
            }
            return TokenKind::And;
        case '\'':
            if (consume('{'))
                return TokenKind::ApostropheOpenBrace;
            else
                return lexApostrophe(info);
        case '(':
            if (!consume('*'))
                return TokenKind::OpenParenthesis;
            else
                return TokenKind::OpenParenthesisStar;
        case ')':
            return TokenKind::CloseParenthesis;
        case '*':
            switch (peek()) {
                case '*':
                    advance();
                    return TokenKind::DoubleStar;
                case '=':
                    advance();
                    return TokenKind::StarEqual;
                case '>':
                    advance();
                    return TokenKind::StarArrow;
                case ')':
                    advance();
                    return TokenKind::StarCloseParenthesis;
                case ':':
                    if (peek(1) == ':' && peek(2) == '*') {
                        advance(3);
                        return TokenKind::StarDoubleColonStar;
                    }
                    return TokenKind::Star;
            }
            return TokenKind::Star;
        case '+':
            switch (peek()) {
                case '+':
                    advance();
                    return TokenKind::DoublePlus;
                case '=':
                    advance();
                    return TokenKind::PlusEqual;
                case ':':
                    advance();
                    return TokenKind::PlusColon;
            }
            return TokenKind::Plus;
        case ',':
            return TokenKind::Comma;
        case '-':
            switch (peek()) {
                case '-':
                    advance();
                    return TokenKind::DoubleMinus;
                case '=':
                    advance();
                    return TokenKind::MinusEqual;
                case ':':
                    advance();
                    return TokenKind::MinusColon;
                case '>':
                    advance();
                    if (consume('>'))
                        return TokenKind::MinusDoubleArrow;
                    else
                        return TokenKind::MinusArrow;
            }
            return TokenKind::Minus;
        case '.':
            if (consume('*'))
                return TokenKind::DotStar;
            else
                return TokenKind::Dot;
        case '/':
            if (consume('='))
                return TokenKind::SlashEqual;
            else
                return TokenKind::Slash;
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
            return lexNumericLiteral(info);
        case ':':
            switch (peek()) {
                case '=':
                    advance();
                    return TokenKind::ColonEquals;
                case '/':
                    advance();
                    return TokenKind::ColonSlash;
                case ':':
                    advance();
                    return TokenKind::DoubleColon;
            }
            return TokenKind::Colon;
        case ';':
            return TokenKind::Semicolon;
        case '<':
            switch (peek()) {
                case '=':
                    advance();
                    return TokenKind::LessThanEquals;
                case '-':
                    if (peek(1) == '>') {
                        advance(2);
                        return TokenKind::LessThanMinusArrow;
                    }
                    return TokenKind::LessThan;
                case '<':
                    advance();
                    switch (peek()) {
                        case '<':
                            if (peek(1) == '=') {
                                advance(2);
                                return TokenKind::TripleLeftShiftEqual;
                            }
                            else {
                                advance();
                                return TokenKind::TripleLeftShift;
                            }
                        case '=':
                            advance();
                            return TokenKind::LeftShiftEqual;
                    }
                    return TokenKind::LeftShift;
            }
            return TokenKind::LessThan;
        case '=':
            switch (peek()) {
                case '=':
                    advance();
                    switch (peek()) {
                        case '=':
                            advance();
                            return TokenKind::TripleEquals;
                        case '?':
                            advance();
                            return TokenKind::DoubleEqualsQuestion;
                    }
                    return TokenKind::DoubleEquals;
                case '>':
                    advance();
                    return TokenKind::EqualsArrow;
            }
            return TokenKind::Equals;
        case '>':
            switch (peek()) {
                case '=':
                    advance();
                    return TokenKind::GreaterThanEquals;
                case '>':
                    advance();
                    switch (peek()) {
                        case '>':
                            if (peek(1) == '=') {
                                advance(2);
                                return TokenKind::TripleRightShiftEqual;
                            }
                            else {
                                advance();
                                return TokenKind::TripleRightShift;
                            }
                        case '=':
                            advance();
                            return TokenKind::RightShiftEqual;
                    }
                    return TokenKind::RightShift;
            }
            return TokenKind::GreaterThan;
        case '?':
            return TokenKind::Question;
        case '@':
            switch (peek()) {
                case '@':
                    advance();
                    return TokenKind::DoubleAt;
                default:
                    return TokenKind::At;
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
            if (getKeywordTable(keywordVersion)->lookup(lexeme(), kind))
                return kind;

            info->extra = IdentifierType::Normal;
            return TokenKind::Identifier;
        }
        case '[':
            return TokenKind::OpenBracket;
        case '\\':
            return lexEscapeSequence(info);
        case ']':
            return TokenKind::CloseBracket;
        case '^':
            switch (peek()) {
                case '~':
                    advance();
                    return TokenKind::XorTilde;
                case '=':
                    advance();
                    return TokenKind::XorEqual;
            }
            return TokenKind::Xor;
        case '`':
            switch (peek()) {
                case '"':
                    advance();
                    return TokenKind::MacroQuote;
                case '`':
                    advance();
                    return TokenKind::MacroPaste;
                case '\\':
                    if (peek(1) == '`' && peek(2) == '"') {
                        advance(3);
                        return TokenKind::MacroEscapedQuote;
                    }
                    return lexDirective(info);
            }
            return lexDirective(info);
        case '{':
            return TokenKind::OpenBrace;
        case '|':
            switch (peek()) {
                case '|':
                    advance();
                    return TokenKind::DoubleOr;
                case '-':
                    if (peek(1) == '>') {
                        advance(2);
                        if (consume('>'))
                            return TokenKind::OrMinusDoubleArrow;
                        else
                            return TokenKind::OrMinusArrow;
                    }
                    return TokenKind::Or;
                case '=':
                    if (peek(1) == '>') {
                        advance(2);
                        return TokenKind::OrEqualsArrow;
                    }
                    else {
                        advance();
                        return TokenKind::OrEqual;
                    }
            }
            return TokenKind::Or;
        case '}':
            return TokenKind::CloseBrace;
        case '~':
            switch (peek()) {
                case '&':
                    advance();
                    return TokenKind::TildeAnd;
                case '|':
                    advance();
                    return TokenKind::TildeOr;
                case '^':
                    advance();
                    return TokenKind::TildeXor;
            }
            return TokenKind::Tilde;
        default:
            if (isASCII(c))
                addDiag(diag::NonPrintableChar, offset);
            else {
                // skip over UTF-8 sequences
                int skip = utf8SeqBytes(c);
                advance(std::min((int)(sourceEnd - sourceBuffer - 1), skip));
                addDiag(diag::UTF8Char, offset);
            }
            return TokenKind::Unknown;
    }
}

void Lexer::lexStringLiteral(Token::Info* info) {
    SmallVectorSized<char, 128> stringBuffer;
    while (true) {
        uint32_t offset = currentOffset();
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
                default:
                    addDiag(diag::UnknownEscapeCode, offset);
                    stringBuffer.append(c);
                    break;
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
            addDiag(diag::EmbeddedNull, offset);
            advance();
        }
        else {
            advance();
            stringBuffer.append(c);
        }
    }

    info->extra = to_string_view(stringBuffer.copy(alloc));
}

TokenKind Lexer::lexEscapeSequence(Token::Info* info) {
    char c = peek();
    if (isWhitespace(c) || c == '\0') {
        // Check for a line continuation sequence.
        if (isNewline(c)) {
            advance();
            if (c == '\r' && peek() == '\n')
                advance();
            return TokenKind::LineContinuation;
        }

        addDiag(diag::EscapedWhitespace, currentOffset());
        return TokenKind::Unknown;
    }

    while (isPrintable(c)) {
        advance();
        c = peek();
        if (isWhitespace(c))
            break;
    }

    info->extra = IdentifierType::Escaped;
    return TokenKind::Identifier;
}

TokenKind Lexer::lexDollarSign(Token::Info* info) {
    scanIdentifier();

    // if length is 1, we just have a dollar sign operator
    if (lexemeLength() == 1)
        return TokenKind::Dollar;

    // otherwise, we have a system identifier
    // check for system keywords
    TokenKind kind = getSystemKeywordKind(lexeme());
    if (kind != TokenKind::Unknown)
        return kind;

    info->extra = IdentifierType::System;
    return TokenKind::Identifier;
}

TokenKind Lexer::lexDirective(Token::Info* info) {
    if (peek() == '\\') {
        // Handle escaped macro names as well.
        advance();
        TokenKind kind = lexEscapeSequence(info);
        if (kind == TokenKind::Identifier) {
            info->extra = SyntaxKind::MacroUsage;
            return TokenKind::Directive;
        }
        return TokenKind::Unknown;
    }

    // store the offset before scanning in order to easily report error locations
    uint32_t startingOffset = currentOffset();
    scanIdentifier();

    // if length is 1, we just have a grave character on its own, which is an error
    if (lexemeLength() == 1) {
        addDiag(diag::MisplacedDirectiveChar, startingOffset);
        return TokenKind::Unknown;
    }

    info->extra = getDirectiveKind(lexeme().substr(1));
    if (!onNewLine && std::get<SyntaxKind>(info->extra) == SyntaxKind::IncludeDirective)
        addDiag(diag::IncludeNotFirstOnLine, startingOffset);

    return TokenKind::Directive;
}

TokenKind Lexer::lexNumericLiteral(Token::Info* info) {
    // have to check for the "1step" magic keyword
    static const char OneStepText[] = "1step";
    for (int i = 0; i < (int)sizeof(OneStepText) - 1; i++) {
        if (peek(i) != OneStepText[i])
            break;
        if (i == sizeof(OneStepText) - 2) {
            advance(sizeof(OneStepText) - 1);
            return TokenKind::OneStep;
        }
    }

    // scan past leading zeros
    while (peek() == '0')
        advance();

    // Keep track of digits as we iterate through them; convert them
    // into logic_t to pass into SVInt parsing method. If it turns out
    // that this is actually a float, we'll go back and populate `floatChars`
    // instead. Since we expect many more ints than floats, it makes sense to
    // not waste time populating that array up front.
    uint32_t startOfNum = currentOffset();
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
                floatChars.append((char)d.value + '0');
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

    bool hasTimeSuffix = false;
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
    // Check for a time literal suffix directly adjacent. Time literal
    // values are always interpreted as doubles.
    else if (lexTimeLiteral(info)) {
        hasTimeSuffix = true;
        if (floatChars.empty())
            populateChars();
    }

    if (!floatChars.empty()) {
        // We have a floating point result. Let the standard library do the heavy lifting of
        // converting and rounding correctly.
        // TODO: change to use std::from_chars once it's available.
        floatChars.append('\0');

        char* end;
        errno = 0;
        double value = strtod(floatChars.data(), &end);
        ASSERT(end == floatChars.end() - 1); // should never error

        // If we had an overflow or underflow, errno is now ERANGE. We can't warn here in case
        // this turns out to actually be a hex literal. Have the token carry this info so someone
        // can check it later if they care.
        info->setReal(value, errno == ERANGE);

        return hasTimeSuffix ? TokenKind::TimeLiteral : TokenKind::RealLiteral;
    }

    // normal numeric literal
    if (digits.empty())
        info->setInt(alloc, SVInt::Zero);
    else {
        static const double BitsPerDecimal = log2(10.0);

        double bitsDbl = ceil(BitsPerDecimal * digits.size());
        bitwidth_t bits;
        if (bitsDbl <= SVInt::MAX_BITS)
            bits = (bitwidth_t)bitsDbl;
        else {
            addDiag(diag::LiteralSizeTooLarge, startOfNum) << (int)SVInt::MAX_BITS;
            bits = SVInt::MAX_BITS;
        }

        SVInt intVal = SVInt::fromDigits(bits, LiteralBase::Decimal, false, false, digits);
        intVal.shrinkToFit();
        info->setInt(alloc, intVal);
    }

    return TokenKind::IntegerLiteral;
}

TokenKind Lexer::lexApostrophe(Token::Info* info) {
    char c = peek();
    switch (c) {
        case '0':
        case '1':
            advance();
            info->setBit((logic_t)getDigitValue(c));
            return TokenKind::UnbasedUnsizedLiteral;
        case 'x':
        case 'X':
            advance();
            info->setBit(logic_t::x);
            return TokenKind::UnbasedUnsizedLiteral;
        case 'Z':
        case 'z':
        case '?':
            advance();
            info->setBit(logic_t::z);
            return TokenKind::UnbasedUnsizedLiteral;

        case 's':
        case 'S':
            advance();
            if (!lexIntegerBase(info, true)) {
                addDiag(diag::ExpectedIntegerBaseAfterSigned, currentOffset());
                info->setNumFlags(LiteralBase::Decimal, true);
            }
            return TokenKind::IntegerBase;

        default:
            if (lexIntegerBase(info, false))
                return TokenKind::IntegerBase;

            // otherwise just an apostrophe token
            return TokenKind::Apostrophe;
    }
}

bool Lexer::lexIntegerBase(Token::Info* info, bool isSigned) {
    LiteralBase base;
    if (literalBaseFromChar(peek(), base)) {
        advance();
        info->setNumFlags(base, isSigned);
        return true;
    }
    return false;
}

bool Lexer::lexTimeLiteral(Token::Info* info) {
#define CASE(c, flag)                          \
    case c:                                    \
        if (peek(1) == 's') {                  \
            advance(2);                        \
            info->setTimeUnit(TimeUnit::flag); \
            return true;                       \
        }                                      \
        break;

    // clang-format off
    switch (peek()) {
        case 's':
            advance();
            info->setTimeUnit(TimeUnit::Seconds);
            return true;
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
    return false;
}

void Lexer::lexTrivia(SmallVector<Trivia>& triviaBuffer) {
    while (true) {
        mark();

        switch (peek()) {
            case ' ':
            case '\t':
            case '\v':
            case '\f':
                advance();
                scanWhitespace(triviaBuffer);
                break;
            case '/':
                switch (peek(1)) {
                    case '/':
                        advance(2);
                        scanLineComment(triviaBuffer);
                        break;
                    case '*': {
                        advance(2);
                        scanBlockComment(triviaBuffer);
                        break;
                    }
                    default:
                        return;
                }
                break;
            case '\r':
                advance();
                consume('\n');
                onNewLine = true;
                addTrivia(TriviaKind::EndOfLine, triviaBuffer);
                break;
            case '\n':
                advance();
                onNewLine = true;
                addTrivia(TriviaKind::EndOfLine, triviaBuffer);
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

void Lexer::scanWhitespace(SmallVector<Trivia>& triviaBuffer) {
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
    addTrivia(TriviaKind::Whitespace, triviaBuffer);
}

void Lexer::scanLineComment(SmallVector<Trivia>& triviaBuffer) {
    while (true) {
        char c = peek();
        if (isNewline(c))
            break;

        if (c == '\0') {
            if (reallyAtEnd())
                break;

            // otherwise just error and ignore
            addDiag(diag::EmbeddedNull, currentOffset());
        }
        advance();
    }
    addTrivia(TriviaKind::LineComment, triviaBuffer);
}

void Lexer::scanBlockComment(SmallVector<Trivia>& triviaBuffer) {
    while (true) {
        char c = peek();
        if (c == '\0') {
            if (reallyAtEnd()) {
                addDiag(diag::UnterminatedBlockComment, currentOffset());
                break;
            }

            // otherwise just error and ignore
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

    addTrivia(TriviaKind::BlockComment, triviaBuffer);
}

void Lexer::addTrivia(TriviaKind kind, SmallVector<Trivia>& triviaBuffer) {
    triviaBuffer.emplace(kind, lexeme());
}

Diagnostic& Lexer::addDiag(DiagCode code, uint32_t offset) {
    errorCount++;
    return diagnostics.add(code, SourceLocation(bufferId, offset));
}

uint32_t Lexer::currentOffset() {
    return (uint32_t)(sourceBuffer - originalBegin);
}

} // namespace slang
