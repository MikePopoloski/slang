#include "slang.h"

namespace {

bool isASCII(char c) {
    return c < 128;
}

bool isPrintable(char c) {
    return c >= 33 && c <= 126;
}

bool isWhitespace(char c) {
    switch (c) {
        case ' ':
        case '\t':
        case '\v':
        case '\f':
        case '\r':
        case '\n':
            return true;
    }
    return false;
}

bool isHorizontalWhitespace(char c) {
    switch (c) {
        case ' ':
        case '\t':
        case '\v':
        case '\f':
            return true;
    }
    return false;
}

bool isNewline(char c) {
    return c == '\r' || c == '\n';
}

bool isDecimalDigitOrUnderscore(char c) {
    return (c >= '0' && c <= '9') || c == '_';
}

bool isOctalDigit(char c) {
    return c >= '0' && c <= '7';
}

bool isHexDigit(char c) {
    return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
}

uint32_t getHexDigitValue(char c) {
    if (c <= '9')
        return c - '0';
    if (c <= 'F')
        return 10 + c - 'A';
    return 10 + c - 'a';
}

char* copyString(slang::Allocator& pool, const char* source, uint32_t length) {
    char* dest = reinterpret_cast<char*>(pool.allocate(length));
    memcpy(dest, source, length);
    return dest;
}

template<typename T>
T* copyArray(slang::Allocator& pool, T* source, uint32_t count) {
    T* dest = reinterpret_cast<T*>(pool.allocate(count * sizeof(T)));
    for (uint32_t i = 0; i < count; i++)
        new (&dest[i]) T(*source++);
    return dest;
}

} // anonymous namespace

namespace slang {

Lexer::Lexer(const char* sourceBuffer, Allocator& pool, Diagnostics& diagnostics) :
    triviaBuffer(32),
    stringBuffer(1024),
    pool(pool),
    diagnostics(diagnostics),
    sourceBuffer(sourceBuffer) {
}

Token* Lexer::lex() {
    // lex leading trivia
    triviaBuffer.clear();
    bool eod = lexTrivia();

    // copy any lexed trivia into standalone memory
    Trivia* trivia = nullptr;
    if (!triviaBuffer.empty())
        trivia = copyArray<Trivia>(pool, triviaBuffer.begin(), triviaBuffer.count());

    {
        // newline in directive mode: issue an EndOfDirective token
        //Token* token = pool.Allocate<Token>(TokenKind::EndOfDirective, false, nullptr);

    }

    // lex the next token
    mark();
    void* data = nullptr;
    TokenKind kind = lexToken(&data);

    return pool.emplace<Token>(kind, false, data, trivia, triviaBuffer.count());
}

TokenKind Lexer::lexToken(void** extraData) {
    char c = peek();
    advance();
    switch (c) {
        case 0: return TokenKind::EndOfFile;
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
            scanStringLiteral(extraData);
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
        case '$': return lexDollarSign(extraData);
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

            scanUnsizedNumericLiteral(extraData);
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
            return lexNumericLiteral(extraData);
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
            auto info = pool.emplace<IdentifierInfo>();
            info->text = lexeme();
            info->type = IdentifierInfo::Normal;
            *extraData = info;
            return TokenKind::Identifier;
        }
        case '[': return TokenKind::OpenBracket;
        case '\\': return lexEscapeSequence(extraData);
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
                    return lexDirective(extraData);
            }
            return lexDirective(extraData);
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
                // TODO: skip over UTF-8 sequences
            }
            return TokenKind::Unknown;
    }
}

void Lexer::scanStringLiteral(void** extraData) {
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
                    charCode = c - '0';
                    if (isOctalDigit(c = peek())) {
                        advance();
                        charCode = (charCode * 8) + c - '0';
                        if (isOctalDigit(c = peek())) {
                            advance();
                            charCode = (charCode * 8) + c - '0';
                            if (charCode > 255) {
                                addError(DiagCode::OctalEscapeCodeTooBig);
                                break;
                            }
                        }
                    }
                    stringBuffer.append(charCode);
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
                        stringBuffer.append(charCode);
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
        else if (c == 0) {
            addError(DiagCode::UnterminatedStringLiteral);
            break;
        }
        else {
            advance();
            stringBuffer.append(c);
        }
    }

    const char* niceText = copyString(pool, stringBuffer.begin(), stringBuffer.count());

    auto info = pool.emplace<StringLiteralInfo>();
    info->rawText = lexeme();
    info->niceText = StringRef(niceText, stringBuffer.count());

    *extraData = info;
}

void Lexer::scanUnsizedNumericLiteral(void** extraData) {
    // should be one four-state digit here

}

void Lexer::scanIdentifier() {
    while (true) {
        switch (peek()) {
            case '0': case '1': case '2': case '3':
            case '4': case '5': case '6': case '7':
            case '8': case '9':
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
            case '_': case '$':
                advance();
                break;
            default:
                return;
        }
    }
}

TokenKind Lexer::lexEscapeSequence(void** extraData) {
    char c = peek();
    if (isWhitespace(c)) {
        addError(DiagCode::EscapedWhitespace);
        return TokenKind::Unknown;
    }

    while (isPrintable(c)) {
        advance();
        c = peek();
        if (isWhitespace(c))
            break;
    }

    auto info = pool.emplace<IdentifierInfo>();
    info->text = lexeme();
    info->type = IdentifierInfo::Escaped;
    *extraData = info;
    return TokenKind::Identifier;
}

TokenKind Lexer::lexDollarSign(void** extraData) {
    scanIdentifier();

    // if length is 1, we just have a dollar sign operator
    if (lexemeLength() == 1)
        return TokenKind::Dollar;

    // otherwise, we have a system identifier
    auto info = pool.emplace<IdentifierInfo>();
    info->text = lexeme();
    info->type = IdentifierInfo::System;
    *extraData = info;
    return TokenKind::SystemIdentifier;
}

TokenKind Lexer::lexDirective(void** extraData) {
    scanIdentifier();

    // if length is 1, we just have a grave character on its own, which is an error
    if (lexemeLength() == 1) {
        addError(DiagCode::MisplacedDirectiveChar);
        return TokenKind::Unknown;
    }

    // lexing behavior changes slightly depending on directives we see
    // TODO:
    DirectiveType type = DirectiveType::Unknown;
    switch (type) {
        case DirectiveType::Unknown:
            return TokenKind::MacroUsage;
        case DirectiveType::Define:
            mode = LexingMode::MacroDefine;
            break;
        case DirectiveType::Include:
            mode = LexingMode::Include;
            break;
        default:
            mode = LexingMode::OtherDirective;
            break;
    }

    return TokenKind::Directive;
}

TokenKind Lexer::lexNumericLiteral(void** extraData) {
    // scan past leading decimal digits; these might be the first part of
    // a fractional number, the size of a vector, or a plain unsigned integer
    while (isDecimalDigitOrUnderscore(peek()))
        advance();

    char c = peek();
    if (isHorizontalWhitespace(c)) {
        // whitespace normally ends a numeric literal, but it's allowed between
        // the size and the base specifier in vector literals, so check if that's what we have here
        int lookahead = 1;
        while (true) {
            char c = peek(lookahead);
            if (isHorizontalWhitespace(c))
                lookahead++;
            else if (c == '\'') {
                advance(lookahead);
                scanVectorLiteral(extraData);
                return TokenKind::IntegerLiteral;
            }
            else
                break;
        }
    }

    switch (peek()) {
        case '\'':
            scanVectorLiteral(extraData);
            return TokenKind::IntegerLiteral;
        case '.':
            // fractional digits
            do {
                advance();
            } while (isDecimalDigitOrUnderscore(peek()));

            // optional exponent
            c = peek();
            return TokenKind::RealLiteral;
        case 'e':
        case 'E':
            advance();
            scanExponent();
            return TokenKind::RealLiteral;
        default:
            return TokenKind::IntegerLiteral;
    }
}

void Lexer::scanVectorLiteral(void** extraData) {

}

void Lexer::scanExponent() {
    char c = peek();
    if (c == '+' || c == '-') {
        advance();
        c = peek();
    }

    if (!isDecimalDigitOrUnderscore(c))
        addError(DiagCode::MissingExponentDigits);
    else {
        do {
            advance();
        } while (isDecimalDigitOrUnderscore(peek()));
    }
}

bool Lexer::lexTrivia() {
    // this function returns true and stops lexing trivia if we find a newline while
    // in directive mode, since that requires an EndOfDirective token to be issued
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
                    case '*':
                        advance(2);
                        if (scanBlockComment())
                            return true;
                        break;
                    default:
                        return false;
                }
                break;
            case '\r':
                advance();
                consume('\n');
                addTrivia(TriviaKind::EndOfLine);
                if (mode != LexingMode::Normal)
                    return true;
                break;
            case '\n':
                advance();
                addTrivia(TriviaKind::EndOfLine);
                if (mode != LexingMode::Normal)
                    return true;
                break;
            case '\\':
                // if we're lexing a directive, this might escape a newline
                if (mode == LexingMode::Normal || !isNewline(peek()))
                    return false;
                advance();
                break;
            default:
                return false;
        }
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
        if (c == 0 || isNewline(c))
            break;

        advance();
    }

    addTrivia(TriviaKind::LineComment);
}

bool Lexer::scanBlockComment() {
    bool eod = false;
    while (true) {
        char c = peek();
        if (c == 0) {
            addError(DiagCode::UnterminatedBlockComment);
            break;
        }
        else if (c == '*' && peek(1) == '/') {
            advance(2);
            break;
        }
        else {
            advance();
            if (mode != LexingMode::Normal && isNewline(c)) {
                // found a newline in a block comment inside a directive; this is not allowed
                // we need to stop lexing trivia and issue an EndOfDirective token after this comment
                addError(DiagCode::SplitBlockCommentInDirective);
                mode = LexingMode::Normal;
                eod = true;
            }
        }
    }

    addTrivia(TriviaKind::BlockComment);
    return eod;
}

void Lexer::addTrivia(TriviaKind kind) {
    triviaBuffer.emplace(kind, lexeme());
}

void Lexer::addError(DiagCode code) {
    diagnostics.add(SyntaxError(code, 0, 0));
}

StringRef Lexer::lexeme() {
    uint32_t length = lexemeLength();
    char* str = copyString(pool, marker, length);
    return StringRef(str, length);
}

} // namespace slang