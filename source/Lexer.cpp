#include <cstdint>
#include <memory>
#include <string>
#include <filesystem>
#include <unordered_map>
#include <deque>
#include <set>

#include "BumpAllocator.h"
#include "Buffer.h"
#include "BufferPool.h"
#include "StringRef.h"
#include "StringTable.h"
#include "Diagnostics.h"
#include "SourceManager.h"
#include "Token.h"
#include "Lexer.h"
#include "CharInfo.h"
#include "StringTable.h"

namespace slang {

SyntaxKind getDirectiveKind(StringRef directive);

Lexer::Lexer(FileID file, SourceText source, BumpAllocator& alloc, Diagnostics& diagnostics) :
    alloc(alloc),
    diagnostics(diagnostics),
    startPointer(source.begin()),
    sourceBuffer(source.begin()),
    sourceEnd(source.end()),
    marker(nullptr),
    file(file)
{
    // detect BOMs so we can give nice errors for invaild encoding
    if (source.length() >= 2) {
        const unsigned char* ubuf = reinterpret_cast<const unsigned char*>(sourceBuffer);
        if ((ubuf[0] == 0xFF && ubuf[1] == 0xFE) ||
            (ubuf[0] == 0xFE && ubuf[1] == 0xFF)) {
            addError(DiagCode::UnicodeBOM, 0);
            advance(2);
        }
        else if (source.length() >= 3) {
            if (ubuf[0] == 0xEF &&
                ubuf[1] == 0xBB &&
                ubuf[2] == 0xBF) {
                addError(DiagCode::UnicodeBOM, 0);
                advance(3);
            }
        }
    }
}

Token* Lexer::lex(LexerMode mode) {
    if (mode == LexerMode::IncludeFileName)
        return lexIncludeFileName();

    // lex leading trivia
    TokenInfo info;
    auto triviaBuffer = triviaPool.get();
    bool directiveMode = mode == LexerMode::Directive;
    if (lexTrivia(triviaBuffer, directiveMode))
        return createToken(TokenKind::EndOfDirective, info, triviaBuffer);

    // lex the next token
    mark();
    TokenKind kind = lexToken(info, directiveMode);
    return createToken(kind, info, triviaBuffer);
}

TokenKind Lexer::lexToken(TokenInfo& info, bool directiveMode) {
    uint32_t offset = currentOffset();
    info.offset = offset;

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
                addError(DiagCode::EmbeddedNull, offset);
                return TokenKind::Unknown;
            }

            // if we're lexing a directive, issue an EndOfDirective before the EndOfFile
            if (directiveMode)
                return TokenKind::EndOfDirective;

            // otherwise, end of file
            return TokenKind::EndOfFile;
        case '!':
            if (consume('=')) {
                switch (peek()) {
                    case '=': advance(); return TokenKind::ExclamationDoubleEquals;
                    case '?': advance(); return TokenKind::ExclamationEqualsQuestion;
                    default: return TokenKind::ExclamationEquals;
                }
            }
            return TokenKind::Exclamation;
        case '"':
            lexStringLiteral(info);
            return TokenKind::StringLiteral;
        case '#':
            switch (peek()) {
                case '#': advance(); return TokenKind::DoubleHash;
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
        case '$': return lexDollarSign(info);
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
                case '=': advance(); return TokenKind::AndEqual;
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
            else if (consume(')'))
                return TokenKind::OpenParenthesisStarCloseParenthesis;
            else
                return TokenKind::OpenParenthesisStar;
        case ')': return TokenKind::CloseParenthesis;
        case '*':
            switch (peek()) {
                case '*': advance(); return TokenKind::DoubleStar;
                case '=': advance(); return TokenKind::StarEqual;
                case '>': advance(); return TokenKind::StarArrow;
                case ')': advance(); return TokenKind::StarCloseParenthesis;
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
                case '+': advance(); return TokenKind::DoublePlus;
                case '=': advance(); return TokenKind::PlusEqual;
                case ':': advance(); return TokenKind::PlusColon;
            }
            return TokenKind::Plus;
        case ',': return TokenKind::Comma;
        case '-':
            switch (peek()) {
                case '-': advance(); return TokenKind::DoubleMinus;
                case '=': advance(); return TokenKind::MinusEqual;
                case ':': advance(); return TokenKind::MinusColon;
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
        case '0': case '1': case '2': case '3':
        case '4': case '5': case '6': case '7':
        case '8': case '9':
            // back up so that lexNumericLiteral can look at this digit again
            sourceBuffer--;
            return lexNumericLiteral(info);
        case ':':
            switch (peek()) {
                case '=': advance(); return TokenKind::ColonEquals;
                case '/': advance(); return TokenKind::ColonSlash;
                case ':': advance(); return TokenKind::DoubleColon;
            }
            return TokenKind::Colon;
        case ';': return TokenKind::Semicolon;
        case '<':
            switch (peek()) {
                case '=': advance(); return TokenKind::LessThanEquals;
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
                        case '=': advance(); return TokenKind::LeftShiftEqual;
                    }
                    return TokenKind::LeftShift;
            }
            return TokenKind::LessThan;
        case '=':
            switch (peek()) {
                case '=':
                    advance();
                    switch (peek()) {
                        case '=': advance(); return TokenKind::TripleEquals;
                        case '?': advance(); return TokenKind::DoubleEqualsQuestion;
                    }
                    return TokenKind::DoubleEquals;
                case '>': advance(); return TokenKind::EqualsArrow;
            }
            return TokenKind::Equals;
        case '>':
            switch (peek()) {
                case '=': advance(); return TokenKind::GreaterThanEquals;
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
                        case '=': advance(); return TokenKind::RightShiftEqual;
                    }
                    return TokenKind::RightShift;
            }
            return TokenKind::GreaterThan;
        case '?': return TokenKind::Question;
        case '@':
            switch (peek()) {
                case '@': advance(); return TokenKind::DoubleAt;
                case '*': advance(); return TokenKind::AtStar;
                default: return TokenKind::At;
            }
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
            scanIdentifier();

            // might be a keyword
            TokenKind kind;
            if (getKeywordTable()->lookup(lexeme(), kind))
                return kind;

            info.identifierType = IdentifierType::Normal;
            return TokenKind::Identifier;
        }
        case '[': return TokenKind::OpenBracket;
        case '\\': return lexEscapeSequence(info);
        case ']': return TokenKind::CloseBracket;
        case '^':
            switch (peek()) {
                case '~': advance(); return TokenKind::XorTilde;
                case '=': advance(); return TokenKind::XorEqual;
            }
            return TokenKind::Xor;
        case '`':
            switch (peek()) {
                case '"': advance(); return TokenKind::MacroQuote;
                case '`': advance(); return TokenKind::MacroPaste;
                case '\\':
                    if (peek(1) == '`' && peek(2) == '"') {
                        advance(3);
                        return TokenKind::MacroEscapedQuote;
                    }
                    return lexDirective(info);
            }
            return lexDirective(info);
        case '{': return TokenKind::OpenBrace;
        case '|':
            switch (peek()) {
                case '|': advance(); return TokenKind::DoubleOr;
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
        case '}': return TokenKind::CloseBrace;
        case '~':
            switch (peek()) {
                case '&': advance(); return TokenKind::TildeAnd;
                case '|': advance(); return TokenKind::TildeOr;
                case '^': advance(); return TokenKind::TildeXor;
            }
            return TokenKind::Tilde;
        default:
            if (isASCII(c))
                addError(DiagCode::NonPrintableChar, offset);
            else {
                // skip over UTF-8 sequences
                advance(utf8SeqBytes(c));
                addError(DiagCode::UTF8Char, offset);
            }
            return TokenKind::Unknown;
    }
}

void Lexer::lexStringLiteral(TokenInfo& info) {
    stringBuffer.clear();

    while (true) {
        uint32_t offset = currentOffset();
        char c = peek();

        if (c == '\\') {
            advance();
            c = peek();
            advance();

            uint32_t charCode;
            switch (c) {
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
                    // octal character code
                    charCode = getDigitValue(c);
                    if (isOctalDigit(c = peek())) {
                        advance();
                        charCode = (charCode * 8) + getDigitValue(c);
                        if (isOctalDigit(c = peek())) {
                            advance();
                            charCode = (charCode * 8) + getDigitValue(c);
                            if (charCode > 255) {
                                addError(DiagCode::OctalEscapeCodeTooBig, offset);
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
                        addError(DiagCode::InvalidHexEscapeCode, offset);
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
                    addError(DiagCode::UnknownEscapeCode, offset);
                    stringBuffer.append(c);
                    break;
            }
        }
        else if (c == '"') {
            advance();
            break;
        }
        else if (isNewline(c)) {
            addError(DiagCode::ExpectedClosingQuote, offset);
            break;
        }
        else if (c == '\0') {
            if (reallyAtEnd()) {
                addError(DiagCode::ExpectedClosingQuote, offset);
                break;
            }

            // otherwise just error and ignore
            addError(DiagCode::EmbeddedNull, offset);
            advance();
        }
        else {
            advance();
            stringBuffer.append(c);
        }
    }

    info.niceText = StringRef(stringBuffer).intern(alloc);
}

TokenKind Lexer::lexEscapeSequence(TokenInfo& info) {
    char c = peek();
    if (isWhitespace(c) || c == '\0') {
        addError(DiagCode::EscapedWhitespace, currentOffset());
        return TokenKind::Unknown;
    }

    while (isPrintable(c)) {
        advance();
        c = peek();
        if (isWhitespace(c))
            break;
    }

    info.identifierType = IdentifierType::Escaped;
    return TokenKind::Identifier;
}

TokenKind Lexer::lexDollarSign(TokenInfo& info) {
    scanIdentifier();

    // if length is 1, we just have a dollar sign operator
    if (lexemeLength() == 1)
        return TokenKind::Dollar;

    // otherwise, we have a system identifier
    // check for system keywords
    TokenKind kind = getSystemKeywordKind(lexeme());
    if (kind != TokenKind::Unknown)
        return kind;

    info.identifierType = IdentifierType::System;
    return TokenKind::SystemIdentifier;
}

TokenKind Lexer::lexDirective(TokenInfo& info) {
    scanIdentifier();

    // if length is 1, we just have a grave character on its own, which is an error
    if (lexemeLength() == 1) {
        addError(DiagCode::MisplacedDirectiveChar, currentOffset() - 1);
        info.directiveKind = SyntaxKind::Unknown;
        return TokenKind::Directive;
    }

    info.directiveKind = getDirectiveKind(lexeme());
    return TokenKind::Directive;
}

Token* Lexer::lexIncludeFileName() {
    // leading whitespace should lex into trivia
    auto triviaBuffer = triviaPool.get();
    if (isHorizontalWhitespace(peek())) {
        mark();
        scanWhitespace(triviaBuffer);
    }

    ArrayRef<Trivia> trivia = triviaBuffer.copy(alloc);
    uint32_t offset = currentOffset();

    mark();
    char delim = peek();
    if (delim != '"' && delim != '<') {
        addError(DiagCode::ExpectedIncludeFileName, offset);
        return Token::missing(alloc, TokenKind::IncludeFileName, SourceLocation(file, offset), trivia);
    }

    advance();
    char c;
    do {
        c = peek();
        if (c == '\0' || isNewline(c)) {
            addError(DiagCode::ExpectedIncludeFileName, offset);
            break;
        }
        advance();
    } while (c != delim);

    StringRef rawText = lexeme();
    return Token::createStringLiteral(alloc, TokenKind::IncludeFileName, SourceLocation(file, offset), trivia, rawText, rawText);
}

TokenKind Lexer::lexNumericLiteral(TokenInfo& info) {
    // have to check for the "1step" magic keyword
    static const char OneStepText[] = "1step";
    for (int i = 0; i < sizeof(OneStepText) - 1; i++) {
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

    // scan past decimal digits; we know we have at least one if we got here
    uint64_t value = 0;
    int digits = 0;
    scanUnsignedNumber(value, digits);

    // check if we have a fractional number here
    info.numericFlags = 0;
    switch (peek()) {
        case '.': {
            // fractional digits
            int decPoint = digits;
            advance();
            if (!isDecimalDigit(peek()))
                addError(DiagCode::MissingFractionalDigits, currentOffset());
            scanUnsignedNumber(value, digits);

            TokenKind result = TokenKind::RealLiteral;
            uint64_t exp = 0;
            bool neg = false;

            char c = peek();
            if (c == 'e' || c == 'E') {
                uint32_t startOfExponent = currentOffset() + 1;
                if (!scanExponent(exp, neg))
                    addError(DiagCode::MissingExponentDigits, startOfExponent);
            }
            else if (lexTimeLiteral(info))
                result = TokenKind::TimeLiteral;

            info.numericValue = computeRealValue(value, decPoint, digits, exp, neg);
            return result;
        }
        case 'e':
        case 'E': {
            // Check if this is an exponent or just something like a hex digit.
            // We disambiguate by always choosing a real if possible; someone
            // downstream might need to fix it up later.
            uint64_t exp;
            bool neg;
            if (scanExponent(exp, neg)) {
                info.numericValue = computeRealValue(value, digits, digits, exp, neg);
                return TokenKind::RealLiteral;
            }
            break;
        }
    }

    // normal signed numeric literal; check for overflow
    if (value > INT32_MAX)
        value = INT32_MAX;
    info.numericValue = (int32_t)value;

    if (lexTimeLiteral(info))
        return TokenKind::TimeLiteral;

    return TokenKind::IntegerLiteral;
}

bool Lexer::scanExponent(uint64_t& value, bool& negative) {
    value = 0;
    negative = false;

    // skip over leading sign
    int index = 1;
    char c = peek(index);
    if (c == '+' || c == '-') {
        negative = c == '-';
        index++;
        c = peek(index);
    }

    // need at least one decimal digit
    if (!isDecimalDigit(c))
        return false;

    // otherwise, we have a real exponent, so skip remaining digits
    int unused = 0;
    advance(index);
    scanUnsignedNumber(value, unused);
    return true;
}

TokenKind Lexer::lexApostrophe(TokenInfo& info) {
    info.numericFlags = 0;
    char c = peek();
    switch (c) {
        case '0':
        case '1':
            advance();
            info.numericValue = (logic_t)(uint8_t)getDigitValue(c);
            return TokenKind::UnbasedUnsizedLiteral;
        case 'x':
        case 'X':
            advance();
            info.numericValue = logic_t::x;
            return TokenKind::UnbasedUnsizedLiteral;
        case 'Z':
        case 'z':
        case '?':
            advance();
            info.numericValue = logic_t::z;
            return TokenKind::UnbasedUnsizedLiteral;

        case 's':
        case 'S':
            advance();
            if (!lexIntegerBase(info))
                addError(DiagCode::ExpectedIntegerBaseAfterSigned, currentOffset());

            info.numericFlags |= NumericTokenFlags::IsSigned;
            return TokenKind::IntegerBase;

        default:
            if (lexIntegerBase(info))
                return TokenKind::IntegerBase;

            // otherwise just an apostrophe token
            return TokenKind::Apostrophe;
    }
}

bool Lexer::lexIntegerBase(TokenInfo& info) {
    switch (peek()) {
        case 'd':
        case 'D':
            advance();
            info.numericFlags = NumericTokenFlags::DecimalBase;
            return true;
        case 'b':
        case 'B':
            advance();
            info.numericFlags = NumericTokenFlags::BinaryBase;
            return true;
        case 'o':
        case 'O':
            advance();
            info.numericFlags = NumericTokenFlags::OctalBase;
            return true;
        case 'h':
        case 'H':
            advance();
            info.numericFlags = NumericTokenFlags::HexBase;
            return true;
    }
    return false;
}

bool Lexer::lexTimeLiteral(TokenInfo& info) {
#define CASE(c, flag) \
    case c: if (peek(1) == 's') { \
        advance(2); \
        info.numericFlags |= NumericTokenFlags::flag; \
        return true; \
    } break;

    switch (peek()) {
        case 's':
            advance();
            info.numericFlags |= NumericTokenFlags::Seconds;
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
    return false;
}

bool Lexer::lexTrivia(Buffer<Trivia>& buffer, bool directiveMode) {
    while (true) {
        mark();

        switch (peek()) {
            case ' ':
            case '\t':
            case '\v':
            case '\f':
                advance();
                scanWhitespace(buffer);
                break;
            case '/':
                switch (peek(1)) {
                    case '/':
                        advance(2);
                        scanLineComment(buffer);
                        break;
                    case '*': {
                        advance(2);
                        if (scanBlockComment(buffer, directiveMode))
                            return true;
                        break;
                    }
                    default:
                        return false;
                }
                break;
            case '\r':
                advance();
                consume('\n');
                addTrivia(TriviaKind::EndOfLine, buffer);
                if (directiveMode)
                    return true;
                break;
            case '\n':
                advance();
                addTrivia(TriviaKind::EndOfLine, buffer);
                if (directiveMode)
                    return true;
                break;
            case '\\':
                // if we're lexing a directive, this might escape a newline
                if (!directiveMode || !isNewline(peek()))
                    return false;
                advance();
                addTrivia(TriviaKind::LineContinuation, buffer);
                break;
            default:
                return false;
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

void Lexer::scanUnsignedNumber(uint64_t& value, int& digits) {
    while (true) {
        char c = peek();
        if (c == '_')
            advance();
        else if (!isDecimalDigit(c))
            return;
        else {
            // After 18 digits stop caring. For normal integers we're going to truncate
            // to 32-bits anyway. For reals, later digits won't have any effect on the result.
            if (digits < MaxMantissaDigits)
                value = (value * 10) + getDigitValue(c);
            digits++;
            advance();
        }
    }
}

void Lexer::scanWhitespace(Buffer<Trivia>& buffer) {
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
    addTrivia(TriviaKind::Whitespace, buffer);
}

void Lexer::scanLineComment(Buffer<Trivia>& buffer) {
    while (true) {
        char c = peek();
        if (isNewline(c))
            break;

        if (c == '\0') {
            if (reallyAtEnd())
                break;
            
            // otherwise just error and ignore
            addError(DiagCode::EmbeddedNull, currentOffset());
        }
        advance();
    }
    addTrivia(TriviaKind::LineComment, buffer);
}

bool Lexer::scanBlockComment(Buffer<Trivia>& buffer, bool directiveMode) {
    bool eod = false;
    while (true) {
        char c = peek();
        if (c == '\0') {
            if (reallyAtEnd()) {
                addError(DiagCode::UnterminatedBlockComment, currentOffset());
                break;
            }

            // otherwise just error and ignore
            addError(DiagCode::EmbeddedNull, currentOffset());
            advance();
        }
        else if (c == '*' && peek(1) == '/') {
            advance(2);
            break;
        }
        else if (c == '/' && peek(1) == '*') {
            // nested block comments disallowed by the standard; ignore and continue
            addError(DiagCode::NestedBlockComment, currentOffset());
            advance(2);
        }
        else {
            if (directiveMode && isNewline(c)) {
                // found a newline in a block comment inside a directive; this is not allowed
                // we need to stop lexing trivia and issue an EndOfDirective token after this comment
                addError(DiagCode::SplitBlockCommentInDirective, currentOffset());
                eod = true;
            }
            advance();
        }
    }
    
    addTrivia(TriviaKind::BlockComment, buffer);
    return eod;
}

Token* Lexer::createToken(TokenKind kind, TokenInfo& info, Buffer<Trivia>& triviaBuffer) {
    auto trivia = triviaBuffer.copy(alloc);
    auto location = SourceLocation(file, info.offset);

    switch (kind) {
        case TokenKind::Unknown:
            return Token::createUnknown(alloc, location, trivia, lexeme());
        case TokenKind::Identifier:
        case TokenKind::SystemIdentifier:
            return Token::createIdentifier(alloc, kind, location, trivia, lexeme(), info.identifierType);
        case TokenKind::IntegerLiteral:
        case TokenKind::IntegerBase:
        case TokenKind::UnbasedUnsizedLiteral:
        case TokenKind::RealLiteral:
        case TokenKind::TimeLiteral:
            return Token::createNumericLiteral(alloc, kind, location, trivia, lexeme(), info.numericValue, info.numericFlags);
        case TokenKind::StringLiteral:
            return Token::createStringLiteral(alloc, kind, location, trivia, lexeme(), info.niceText);
        case TokenKind::Directive:
            return Token::createDirective(alloc, kind, location, trivia, lexeme(), info.directiveKind);
        default:
            return Token::createSimple(alloc, kind, location, trivia);
    }
}

void Lexer::addTrivia(TriviaKind kind, Buffer<Trivia>& buffer) {
    buffer.emplace(kind, lexeme());
}

void Lexer::addError(DiagCode code, uint32_t offset) {
    diagnostics.emplace(code, SourceLocation(file, offset));
}

} // namespace slang