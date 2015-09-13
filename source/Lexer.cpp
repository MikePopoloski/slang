#include <cstdint>
#include <memory>
#include <string>
#include <filesystem>
#include <unordered_map>
#include <deque>
#include <set>

#include "BumpAllocator.h"
#include "Buffer.h"
#include "StringRef.h"
#include "StringTable.h"
#include "Diagnostics.h"
#include "SourceTracker.h"
#include "Token.h"
#include "Lexer.h"
#include "Preprocessor.h"
#include "CharInfo.h"
#include "StringTable.h"
#include "SyntaxFacts.h"

namespace {

const int MaxMantissaDigits = 18;
const int MaxExponent = 511;

const double powersOf10[] = {
    10.0,
    100.0,
    1.0e4,
    1.0e8,
    1.0e16,
    1.0e32,
    1.0e64,
    1.0e128,
    1.0e256
};

template<typename T>
slang::ArrayRef<T> copyArray(slang::BumpAllocator& alloc, const slang::Buffer<T>& buffer) {
    uint32_t count = buffer.count();
    if (count == 0)
        return slang::ArrayRef<T>(nullptr, 0);

    const T* source = buffer.cbegin();
    T* dest = reinterpret_cast<T*>(alloc.allocate(count * sizeof(T)));
    for (uint32_t i = 0; i < count; i++)
        new (&dest[i]) T(*source++);
    return slang::ArrayRef<T>(dest, count);
}

bool composeDouble(double fraction, int exp, double& result) {
    bool neg = false;
    if (exp < 0) {
        neg = true;
        exp = -exp;
    }

    if (exp > MaxExponent)
        exp = MaxExponent;

    double dblExp = 1.0;
    for (auto d = powersOf10; exp != 0; exp >>= 1, d++) {
        if (exp & 0x1)
            dblExp *= *d;
    }

    if (neg)
        fraction /= dblExp;
    else
        fraction *= dblExp;

    result = fraction;
    return std::isfinite(result);
}

} // anonymous namespace

namespace slang {

Lexer::Lexer(FileID file, const SourceText& source, Preprocessor& preprocessor) :
    preprocessor(preprocessor),
    alloc(preprocessor.getAllocator()),
    sourceBuffer(source.begin()),
    sourceEnd(source.end()),
    marker(nullptr),
    file(file),
    inDirective(false) {

    // detect BOMs so we can give nice errors for invaild encoding
    if (source.length() >= 2) {
        const unsigned char* ubuf = reinterpret_cast<const unsigned char*>(sourceBuffer);
        if ((ubuf[0] == 0xFF && ubuf[1] == 0xFE) ||
            (ubuf[0] == 0xFE && ubuf[1] == 0xFF)) {
            addError(DiagCode::UnicodeBOM);
            advance(2);
        }
        else if (source.length() >= 3) {
            if (ubuf[0] == 0xEF &&
                ubuf[1] == 0xBB &&
                ubuf[2] == 0xBF) {
                addError(DiagCode::UnicodeBOM);
                advance(3);
            }
        }
    }
}

Token* Lexer::lex() {
    // lex leading trivia
    triviaBuffer.clear();
    bool eod = lexTrivia();
    ArrayRef<Trivia*> trivia = copyArray(alloc, triviaBuffer);

    // return an eod token right away if we detected we need one
    if (eod)
        return Token::createSimple(alloc, TokenKind::EndOfDirective, trivia);

    // lex the next token
    mark();
    TokenInfo info;
    TokenKind kind = lexToken(info);
    switch (kind) {
        case TokenKind::Unknown:
            return Token::createUnknown(alloc, trivia, lexeme());
        case TokenKind::Identifier:
        case TokenKind::SystemIdentifier:
            return Token::createIdentifier(alloc, kind, trivia, lexeme(), info.identifierType);
        case TokenKind::IntegerLiteral:
        case TokenKind::RealLiteral:
            return Token::createNumericLiteral(alloc, kind, trivia, lexeme(), info.numericValue);
        case TokenKind::StringLiteral:
            return Token::createStringLiteral(alloc, kind, trivia, lexeme(), info.niceText);
        case TokenKind::Directive:
            return Token::createDirective(alloc, kind, trivia, lexeme(), info.directiveKind);
        default:
            return Token::createSimple(alloc, kind, trivia);
    }
}

Token* Lexer::lexDirectiveMode() {
    bool saveMode = inDirective;
    inDirective = true;

    Token* result = lex();
    inDirective = saveMode;

    return result;
}

Token* Lexer::lexIncludeFileName() {
    // TODO: trivia

    char delim = peek();
    if (delim != '"' && delim != '<') {
        addError(DiagCode::ExpectedIncludeFileName);
        return Token::missing(alloc, TokenKind::IncludeFileName);
    }

    char c;
    do {
        c = peek();
        if (c == '\0' || isNewline(c)) {
            addError(DiagCode::ExpectedEndOfIncludeFileName);
            break;
        }
        advance();
    } while (c != delim);

    uint32_t len = lexemeLength() - 1;
    if (c == delim)
        len--;

    StringRef rawText = lexeme();
    return Token::createStringLiteral(alloc, TokenKind::IncludeFileName, nullptr, rawText, rawText.subString(1, len));
}

TokenKind Lexer::lexToken(TokenInfo& info) {
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
                addError(DiagCode::EmbeddedNull);
                return TokenKind::Unknown;
            }

            // if we're lexing a directive, issue an EndOfDirective before the EndOfFile
            if (inDirective)
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
            // either an unsized numeric literal, or a '{ range open sequence
            if (consume('{'))
                return TokenKind::ApostropheOpenBrace;

            lexUnsizedNumericLiteral(info);
            return TokenKind::IntegerLiteral;
        case '(':
            if (consume('*'))
                return TokenKind::OpenParenthesisStar;
            else
                return TokenKind::OpenParenthesis;
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
            if (consume('@'))
                return TokenKind::DoubleAt;
            else
                return TokenKind::At;
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
            TokenKind kind = preprocessor.lookupKeyword(lexeme());
            if (kind != TokenKind::Unknown)
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
                addError(DiagCode::NonPrintableChar);
            else {
                // skip over UTF-8 sequences
                advance(utf8SeqBytes(c));
                addError(DiagCode::UTF8Char);
            }
            return TokenKind::Unknown;
    }
}

void Lexer::lexStringLiteral(TokenInfo& info) {
    stringBuffer.clear();

    while (true) {
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
                                addError(DiagCode::OctalEscapeCodeTooBig);
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
                        addError(DiagCode::InvalidHexEscapeCode);
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
                    addError(DiagCode::UnknownEscapeCode);
                    stringBuffer.append(c);
                    break;
            }
        }
        else if (c == '"') {
            advance();
            break;
        }
        else if (isNewline(c)) {
            addError(DiagCode::NewlineInStringLiteral);
            break;
        }
        else if (c == '\0') {
            if (reallyAtEnd()) {
                addError(DiagCode::UnterminatedStringLiteral);
                break;
            }

            // otherwise just error and ignore
            addError(DiagCode::EmbeddedNull);
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
        addError(DiagCode::EscapedWhitespace);
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
    info.identifierType = IdentifierType::System;
    return TokenKind::SystemIdentifier;
}

TokenKind Lexer::lexDirective(TokenInfo& info) {
    scanIdentifier();

    // if length is 1, we just have a grave character on its own, which is an error
    if (lexemeLength() == 1) {
        addError(DiagCode::MisplacedDirectiveChar);
        return TokenKind::Unknown;
    }

    info.directiveKind = getDirectiveKind(lexeme());
    return TokenKind::Directive;
}

TokenKind Lexer::lexNumericLiteral(TokenInfo& info) {
    // skip over leading zeros
    char c;
    while ((c = peek()) == '0')
        advance();

    // scan past leading decimal digits; these might be the first part of
    // a fractional number, the size of a vector, or a plain unsigned integer
    uint64_t unsignedVal = 0;
    int digits = 0;
    c = scanUnsignedNumber(c, unsignedVal, digits);

    // whitespace normally ends a numeric literal, but it's allowed between
    // the size and the base specifier in vector literals, so check if that's what we have here
    int lookahead = findNextNonWhitespace();
    if (lookahead > 0 && peek(lookahead) == '\'') {
        advance(lookahead + 1);
        lexVectorLiteral(info, unsignedVal);
        return TokenKind::IntegerLiteral;
    }

    switch (peek()) {
        case '\'':
            advance();
            lexVectorLiteral(info, unsignedVal);
            return TokenKind::IntegerLiteral;
        case '.': {
            // fractional digits
            int decPoint = digits;
            advance();
            c = peek();
            if (!isDecimalDigit(c))
                addError(DiagCode::MissingFractionalDigits);

            c = scanUnsignedNumber(peek(), unsignedVal, digits);
            lexRealLiteral(
                info,
                unsignedVal,
                decPoint,
                digits,
                c == 'e' || c == 'E'
            );
            return TokenKind::RealLiteral;
        }
        case 'e':
        case 'E':
            lexRealLiteral(
                info,
                unsignedVal,
                digits,     // decimal point is after all digits
                digits,
                true        // yep, we have an exponent
            );
            return TokenKind::RealLiteral;
        default:
            // normal signed numeric literal; check for 32-bit overflow
            if (unsignedVal > INT32_MAX) {
                unsignedVal = INT32_MAX;
                addError(DiagCode::SignedLiteralTooLarge);
            }
            info.numericValue = (int32_t)unsignedVal;
            return TokenKind::IntegerLiteral;
    }
}

void Lexer::lexRealLiteral(TokenInfo& info, uint64_t value, int decPoint, int digits, bool exponent) {
    bool neg = false;
    uint64_t expVal = 0;

    if (exponent) {
        advance();

        // skip over leading zeros
        char c = peek();
        while ((c = peek()) == '0')
            advance();

        if (c == '+')
            advance();
        else if (c == '-') {
            neg = true;
            advance();
        }

        c = peek();
        if (!isDecimalDigit(c))
            addError(DiagCode::MissingExponentDigits);
        else {
            int unusedDigits = 0;
            scanUnsignedNumber(c, expVal, unusedDigits);
        }
    }

    int fracExp = decPoint - std::min(digits, MaxMantissaDigits);
    int exp;
    if (neg)
        exp = fracExp - int(expVal);
    else
        exp = fracExp + int(expVal);

    double result;
    if (!composeDouble(double(value), exp, result))
        addError(DiagCode::RealExponentTooLarge);

    info.numericValue = result;
}

void Lexer::lexVectorLiteral(TokenInfo& info, uint64_t size64) {
    // error checking on the size, plus coerce to 32-bit
    uint32_t size32 = 0;
    if (size64 == 0)
        addError(DiagCode::IntegerSizeZero);
    else {
        if (size64 > UINT32_MAX) {
            size64 = UINT32_MAX;
            addError(DiagCode::IntegerSizeTooLarge);
        }
        size32 = (uint32_t)size64;
    }

    // check for signed specifier
    bool isSigned = false;
    char c = peek();
    if (c == 's' || c == 'S') {
        isSigned = true;
        advance();
        c = peek();
    }

    vectorBuilder.start(size32, isSigned);

    // next character needs to be the base
    switch (c) {
        case 'd':
        case 'D':
            advance();
            lexVectorDigits<isDecimalDigit, getDigitValue>(info);
            break;
        case 'o':
        case 'O':
            advance();
            lexVectorDigits<isOctalDigit, getDigitValue>(info);
            break;
        case 'h':
        case 'H':
            advance();
            lexVectorDigits<isHexDigit, getHexDigitValue>(info);
            break;
        case 'b':
        case 'B':
            advance();
            lexVectorDigits<isBinaryDigit, getDigitValue>(info);
            break;
        default:
            // error case
            addError(DiagCode::MissingVectorBase);
            info.numericValue = 0;
            break;
    }
}

void Lexer::lexUnsizedNumericLiteral(TokenInfo& info) {
    vectorBuilder.startUnsized();
    char c = peek();
    switch (c) {
        case 'd':
        case 'D':
            advance();
            lexVectorDigits<isDecimalDigit, getDigitValue>(info);
            break;
        case 'o':
        case 'O':
            advance();
            lexVectorDigits<isOctalDigit, getDigitValue>(info);
            break;
        case 'h':
        case 'H':
            advance();
            lexVectorDigits<isHexDigit, getHexDigitValue>(info);
            break;
        case 'b':
        case 'B':
            advance();
            lexVectorDigits<isBinaryDigit, getDigitValue>(info);
            break;
        case '0':
        case '1':
            advance();
            info.numericValue = (logic_t)(uint8_t)getDigitValue(c);
            break;
        case 'x':
        case 'X':
            advance();
            info.numericValue = logic_t::x;
            break;
        case 'Z':
        case 'z':
            advance();
            info.numericValue = logic_t::z;
            break;
        default:
            // error case
            addError(DiagCode::InvalidUnsizedLiteral);
            info.numericValue = 0;
            break;
    }
}

template<bool(*IsDigitFunc)(char), uint32_t(*ValueFunc)(char)>
void Lexer::lexVectorDigits(TokenInfo& info) {
    // skip leading whitespace
    int lookahead = findNextNonWhitespace();
    char c = peek(lookahead);
    if (!IsDigitFunc(c) && !isLogicDigit(c)) {
        addError(DiagCode::MissingVectorDigits);
        info.numericValue = 0;
        return;
    }

    advance(lookahead);

    while (true) {
        c = peek();
        switch (c) {
            case '_':
                break;
            case 'z':
            case 'Z':
            case '?':
                vectorBuilder.addDigit(logic_t::z);
                break;
            case 'x':
            case 'X':
                vectorBuilder.addDigit(logic_t::x);
                break;
            default:
                if (IsDigitFunc(c))
                    vectorBuilder.addDigit((char)ValueFunc(c));
                else {
                    info.numericValue = vectorBuilder.toVector();
                    return;
                }
        }
        advance();
    }
}

bool Lexer::lexTrivia() {
    while (true) {
        mark();

        switch (peek()) {
            case ' ':
            case '\t':
            case '\v':
            case '\f':
                advance();
                scanWhitespace();
                addTrivia(TriviaKind::Whitespace);
                break;
            case '/':
                switch (peek(1)) {
                    case '/':
                        advance(2);
                        scanLineComment();
                        break;
                    case '*': {
                        advance(2);
                        if (scanBlockComment())
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
                addTrivia(TriviaKind::EndOfLine);
                if (inDirective)
                    return true;
                break;
            case '\n':
                advance();
                addTrivia(TriviaKind::EndOfLine);
                if (inDirective)
                    return true;
                break;
            case '`':
                // can't recursively enter directive mode
                // this is probably a token paste operator or macro usage
                if (inDirective)
                    return false;
                lexDirectiveTrivia();
                break;
            case '\\':
                // if we're lexing a directive, this might escape a newline
                if (!inDirective || !isNewline(peek()))
                    return false;
                advance();
                addTrivia(TriviaKind::LineContinuation);
                break;
            default:
                return false;
        }
    }
}

void Lexer::lexDirectiveTrivia() {
    // make a copy of the trivia buffer locally, because the preprocessor is going to
    // call back in to lex() and that would stomp over the trivia we've already collected
    Buffer<Trivia*> saveTrivia(triviaBuffer.count() + 1);
    saveTrivia.appendRange(triviaBuffer);

    inDirective = true;
    Trivia* directive = preprocessor.parseDirective(this);
    ASSERT(directive);
    saveTrivia.append(directive);
    inDirective = false;

    // copy trivia back
    triviaBuffer.clear();
    triviaBuffer.appendRange(saveTrivia);
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

char Lexer::scanUnsignedNumber(char c, uint64_t& unsignedVal, int& digits) {
    while (true) {
        if (isDecimalDigit(c)) {
            // After 18 digits, stop caring. For normal integers, we're going to truncate
            // to 32-bits anyway. For reals, later digits won't have any effect on the result.
            if (digits < MaxMantissaDigits)
                unsignedVal = (unsignedVal * 10) + getDigitValue(c);
            digits++;
        }
        else if (c != '_')
            break;

        advance();
        c = peek();
    }
    return c;
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
            addError(DiagCode::EmbeddedNull);
        }
        advance();
    }
    addTrivia(TriviaKind::LineComment);
}

bool Lexer::scanBlockComment() {
    bool eod = false;
    while (true) {
        char c = peek();
        if (c == '\0') {
            if (reallyAtEnd()) {
                addError(DiagCode::UnterminatedBlockComment);
                break;
            }

            // otherwise just error and ignore
            addError(DiagCode::EmbeddedNull);
        }
        else if (c == '*' && peek(1) == '/') {
            advance(2);
            break;
        }
        else if (c == '/' && peek(1) == '*') {
            // nested block comments disallowed by the standard; ignore and continue
            advance(2);
            addError(DiagCode::NestedBlockComment);
        }
        else {
            advance();
            if (inDirective && isNewline(c)) {
                // found a newline in a block comment inside a directive; this is not allowed
                // we need to stop lexing trivia and issue an EndOfDirective token after this comment
                addError(DiagCode::SplitBlockCommentInDirective);
                eod = true;
            }
        }
    }
    
    addTrivia(TriviaKind::BlockComment);
    return eod;
}

int Lexer::findNextNonWhitespace() {
    int lookahead = 0;
    char c;
    while (isHorizontalWhitespace(c = peek(lookahead)))
        lookahead++;
    return lookahead;
}

void Lexer::addTrivia(TriviaKind kind) {
    triviaBuffer.append(alloc.emplace<SimpleTrivia>(kind, lexeme()));
}

void Lexer::addError(DiagCode code) {
    preprocessor.getDiagnostics().add(SyntaxError(code, 0, 0));
}

} // namespace slang