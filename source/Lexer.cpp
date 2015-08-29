#include "slang.h"

namespace {

bool IsASCII(char c) {
    return c < 128;
}

bool IsPrintable(char c) {
    return c >= 33 && c <= 126;
}

bool IsWhitespace(char c) {
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

bool IsHorizontalWhitespace(char c) {
    switch (c) {
        case ' ':
        case '\t':
        case '\v':
        case '\f':
            return true;
    }
    return false;
}

bool IsNewline(char c) {
    return c == '\r' || c == '\n';
}

bool IsDecimalDigit(char c) {
    return (c >= '0' && c <= '9') || c == '_';
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

Lexer::Lexer(const char* sourceBuffer, Allocator& pool)
    : triviaBuffer(32),
      stringBuffer(1024),
      pool(pool),
      sourceBuffer(sourceBuffer) {
}

Token* Lexer::Lex() {
    // lex leading trivia
    triviaBuffer.clear();
    bool eod = LexTrivia();

    // copy any lexed trivia into standalone memory
    Trivia* trivia = nullptr;
    if (!triviaBuffer.empty())
        trivia = copyArray<Trivia>(pool, triviaBuffer.begin(), triviaBuffer.count());
    
    {
        // newline in directive mode: issue an EndOfDirective token
        //Token* token = pool.Allocate<Token>(TokenKind::EndOfDirective, false, nullptr);

    }

    // lex the next token
    Mark();
    void* data = nullptr;
    TokenKind kind = LexToken(&data);

    return pool.emplace<Token>(kind, false, data, trivia, triviaBuffer.count());
}

TokenKind Lexer::LexToken(void** extraData) {
    char c = Next();
    switch (c) {
        case 0: return TokenKind::EndOfFile;
        case '!':
            if (Consume('=')) {
                switch (Peek()) {
                    case '=': Advance(); return TokenKind::ExclamationDoubleEquals;
                    case '?': Advance(); return TokenKind::ExclamationEqualsQuestion;
                    default: return TokenKind::ExclamationEquals;
                }
            }
            return TokenKind::Exclamation;
        case '"':
            ScanStringLiteral(extraData);
            return TokenKind::StringLiteral;
        case '#':
            switch (Peek()) {
                case '#': Advance(); return TokenKind::DoubleHash;
                case '-':
                    if (Peek(1) == '#') {
                        Advance(2);
                        return TokenKind::HashMinusHash;
                    }
                    // #- isn't a token, so just return a hash
                    return TokenKind::Hash;
                case '=':
                    if (Peek(1) == '#') {
                        Advance(2);
                        return TokenKind::HashEqualsHash;
                    }
                    // #= isn't a token, so just return a hash
                    return TokenKind::Hash;
            }
            return TokenKind::Hash;
        case '$': return ScanDollarSign(extraData);
        case '%':
            if (Consume('='))
                return TokenKind::PercentEqual;
            return TokenKind::Percent;
        case '&':
            switch (Peek()) {
                case '&':
                    Advance();
                    if (Consume('&'))
                        return TokenKind::TripleAnd;
                    else
                        return TokenKind::DoubleAnd;
                case '=': Advance(); return TokenKind::AndEqual;
            }
            return TokenKind::And;
        case '\'':
            // either an unsized numeric literal, or a '{ range open sequence
            if (Consume('{'))
                return TokenKind::ApostropheOpenBrace;

            ScanUnsizedNumericLiteral(extraData);
            return TokenKind::IntegerLiteral;
        case '(':
            if (Consume('*'))
                return TokenKind::OpenParenthesisStar;
            else
                return TokenKind::OpenParenthesis;
        case ')': return TokenKind::CloseParenthesis;
        case '*':
            switch (Peek()) {
                case '*': Advance(); return TokenKind::DoubleStar;
                case '=': Advance(); return TokenKind::StarEqual;
                case '>': Advance(); return TokenKind::StarArrow;
                case ')': Advance(); return TokenKind::StarCloseParenthesis;
                case ':':
                    if (Peek(1) == ':' && Peek(2) == '*') {
                        Advance(3);
                        return TokenKind::StarDoubleColonStar;
                    }
                    return TokenKind::Star;
            }
            return TokenKind::Star;
        case '+':
            switch (Peek()) {
                case '+': Advance(); return TokenKind::DoublePlus;
                case '=': Advance(); return TokenKind::PlusEqual;
                case ':': Advance(); return TokenKind::PlusColon;
            }
            return TokenKind::Plus;
        case ',': return TokenKind::Comma;
        case '-':
            switch (Peek()) {
                case '-': Advance(); return TokenKind::DoubleMinus;
                case '=': Advance(); return TokenKind::MinusEqual;
                case ':': Advance(); return TokenKind::MinusColon;
                case '>':
                    Advance();
                    if (Consume('>'))
                        return TokenKind::MinusDoubleArrow;
                    else
                        return TokenKind::MinusArrow;
            }
            return TokenKind::Minus;
        case '.':
            if (Consume('*'))
                return TokenKind::DotStar;
            else
                return TokenKind::Dot;
        case '/':
            if (Consume('='))
                return TokenKind::SlashEqual;
            else
                return TokenKind::Slash;
        case '0': case '1': case '2': case '3':
        case '4': case '5': case '6': case '7':
        case '8': case '9':
            return ScanNumericLiteral(extraData);
        case ':':
            switch (Peek()) {
                case '=': Advance(); return TokenKind::ColonEquals;
                case '/': Advance(); return TokenKind::ColonSlash;
                case ':': Advance(); return TokenKind::DoubleColon;
            }
            return TokenKind::Colon;
        case ';': return TokenKind::Semicolon;
        case '<':
            switch (Peek()) {
                case '=': Advance(); return TokenKind::LessThanEquals;
                case '-':
                    if (Peek(1) == '>') {
                        Advance(2);
                        return TokenKind::LessThanMinusArrow;
                    }
                    return TokenKind::LessThan;
                case '<':
                    Advance();
                    switch (Peek()) {
                        case '<':
                            if (Peek(1) == '=') {
                                Advance(2);
                                return TokenKind::TripleLeftShiftEqual;
                            }
                            else {
                                Advance();
                                return TokenKind::TripleLeftShift;
                            }
                        case '=': Advance(); return TokenKind::LeftShiftEqual;
                    }
                    return TokenKind::LeftShift;
            }
            return TokenKind::LessThan;
        case '=':
            switch (Peek()) {
                case '=':
                    Advance();
                    switch (Peek()) {
                        case '=': Advance(); return TokenKind::TripleEquals;
                        case '?': Advance(); return TokenKind::DoubleEqualsQuestion;
                    }
                    return TokenKind::DoubleEquals;
                case '>': Advance(); return TokenKind::EqualsArrow;
            }
            return TokenKind::Equals;
        case '>':
            switch (Peek()) {
                case '=': Advance(); return TokenKind::GreaterThanEquals;
                case '>':
                    Advance();
                    switch (Peek()) {
                        case '>':
                            if (Peek(1) == '=') {
                                Advance(2);
                                return TokenKind::TripleRightShiftEqual;
                            }
                            else {
                                Advance();
                                return TokenKind::TripleRightShift;
                            }
                        case '=': Advance(); return TokenKind::RightShiftEqual;
                    }
                    return TokenKind::RightShift;
            }
            return TokenKind::GreaterThan;
        case '?': return TokenKind::Question;
        case '@':
            if (Consume('@'))
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
            ScanIdentifier();
            auto info = pool.emplace<IdentifierInfo>();
            info->text = GetCurrentLexeme();
            info->type = IdentifierInfo::Normal;
            *extraData = info;
            return TokenKind::Identifier;
        }
        case '[': return TokenKind::OpenBracket;
        case '\\': return ScanEscapeSequence(extraData);
        case ']': return TokenKind::CloseBracket;
        case '^':
            switch (Peek()) {
                case '~': Advance(); return TokenKind::XorTilde;
                case '=': Advance(); return TokenKind::XorEqual;
            }
            return TokenKind::Xor;
        case '`':
            switch (Peek()) {
                case '"': Advance(); return TokenKind::MacroQuote;
                case '`': Advance(); return TokenKind::MacroPaste;
                case '\\':
                    if (Peek(1) == '`' && Peek(2) == '"') {
                        Advance(3);
                        return TokenKind::MacroEscapedQuote;
                    }
                    return ScanDirective(extraData);
            }
            return ScanDirective(extraData);
        case '{': return TokenKind::OpenBrace;
        case '|':
            switch (Peek()) {
                case '|': Advance(); return TokenKind::DoubleOr;
                case '-':
                    if (Peek(1) == '>') {
                        Advance(2);
                        return TokenKind::OrMinusArrow;
                    }
                    return TokenKind::Or;
                case '=':
                    if (Peek(1) == '>') {
                        Advance(2);
                        return TokenKind::OrEqualsArrow;
                    }
                    else {
                        Advance();
                        return TokenKind::OrEqual;
                    }
            }
            return TokenKind::Or;
        case '}': return TokenKind::CloseBrace;
        case '~':
            switch (Peek()) {
                case '&': Advance(); return TokenKind::TildeAnd;
                case '|': Advance(); return TokenKind::TildeOr;
                case '^': Advance(); return TokenKind::TildeXor;
            }
            return TokenKind::Tilde;
        default:
            if (IsASCII(c))
                AddError(DiagCode::NonPrintableChar);
            else {
                // TODO: skip over UTF-8 sequences
            }
            return TokenKind::Unknown;
    }
}

void Lexer::ScanStringLiteral(void** extraData) {
    stringBuffer.clear();

    while (true) {
        char c = Peek();
        if (c == '\\') {
            Advance();
            c = Next();
            switch (c) {
                // simple escape codes
                case 'n': stringBuffer.append('\n'); break;
                case 't': stringBuffer.append('\t'); break;
                case '\\': stringBuffer.append('\\'); break;
                case '"': stringBuffer.append('"'); break;
                case 'v': stringBuffer.append('\v'); break;
                case 'f': stringBuffer.append('\f'); break;
                case 'a': stringBuffer.append('\a'); break;

                // newlines are escaped (and ignored) by backslash
                case '\n': break;
                case '\r': Consume('\n'); break;
                    
                // TODO: digit codes
                // TODO: error handling
            }
        }
        else if (c == '"') {
            Advance();
            break;
        }
        else if (IsNewline(c)) {
            AddError(DiagCode::NewlineInStringLiteral);
            break;
        }
        else if (c == 0) {
            AddError(DiagCode::UnterminatedStringLiteral);
            break;
        }
        else {
            Advance();
            stringBuffer.append(c);
        }
    }

    const char* niceText = copyString(pool, stringBuffer.begin(), stringBuffer.count());

    auto info = pool.emplace<StringLiteralInfo>();
    info->rawText = GetCurrentLexeme();
    info->niceText = StringRef(niceText, stringBuffer.count());

    *extraData = info;
}

void Lexer::ScanUnsizedNumericLiteral(void** extraData) {
    // should be one four-state digit here

}

void Lexer::ScanIdentifier() {
    while (true) {
        switch (Peek()) {
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
                Advance();
                break;
            default:
                return;
        }
    }
}

TokenKind Lexer::ScanEscapeSequence(void** extraData) {
    char c = Peek();
    if (IsWhitespace(c)) {
        AddError(DiagCode::EscapedWhitespace);
        return TokenKind::Unknown;
    }

    while (IsPrintable(c)) {
        Advance();
        c = Peek();
        if (IsWhitespace(c))
            break;
    }

    auto info = pool.emplace<IdentifierInfo>();
    info->text = GetCurrentLexeme();
    info->type = IdentifierInfo::Escaped;
    *extraData = info;
    return TokenKind::Identifier;
}

TokenKind Lexer::ScanDollarSign(void** extraData) {
    ScanIdentifier();

    // if length is 1, we just have a dollar sign operator
    if (GetCurrentLexemeLength() == 1)
        return TokenKind::Dollar;

    // otherwise, we have a system identifier
    auto info = pool.emplace<IdentifierInfo>();
    info->text = GetCurrentLexeme();
    info->type = IdentifierInfo::System;
    *extraData = info;
    return TokenKind::SystemIdentifier;
}

TokenKind Lexer::ScanDirective(void** extraData) {
    ScanIdentifier();

    // if length is 1, we just have a grave character on its own, which is an error
    if (GetCurrentLexemeLength() == 1) {
        AddError(DiagCode::MisplacedDirectiveChar);
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

TokenKind Lexer::ScanNumericLiteral(void** extraData) {
    // scan past leading decimal digits; these might be the first part of
    // a fractional number, the size of a vector, or a plain unsigned integer
    while (IsDecimalDigit(Peek()))
        Advance();

    char c = Peek();
    if (IsHorizontalWhitespace(c)) {
        // whitespace normally ends a numeric literal, but it's allowed between
        // the size and the base specifier in vector literals, so check if that's what we have here
        int lookahead = 1;
        while (true) {
            char c = Peek(lookahead);
            if (IsHorizontalWhitespace(c))
                lookahead++;
            else if (c == '\'') {
                Advance(lookahead);
                ScanVectorLiteral(extraData);
                return TokenKind::IntegerLiteral;
            }
            else
                break;
        }
    }

    switch (Peek()) {
        case '\'':
            ScanVectorLiteral(extraData);
            return TokenKind::IntegerLiteral;
        case '.':
            // fractional digits
            do {
                Advance();
            } while (IsDecimalDigit(Peek()));

            // optional exponent
            c = Peek();
            return TokenKind::RealLiteral;
        case 'e':
        case 'E':
            Advance();
            ScanExponent();
            return TokenKind::RealLiteral;
        default:
            return TokenKind::IntegerLiteral;
    }
}

void Lexer::ScanVectorLiteral(void** extraData) {

}

void Lexer::ScanExponent() {
    char c = Peek();
    if (c == '+' || c == '-') {
        Advance();
        c = Peek();
    }

    if (!IsDecimalDigit(c))
        AddError(DiagCode::MissingExponentDigits);
    else {
        do {
            Advance();
        } while (IsDecimalDigit(Peek()));
    }
}

bool Lexer::LexTrivia() {
    // this function returns true and stops lexing trivia if we find a newline while
    // in directive mode, since that requires an EndOfDirective token to be issued
    while (true) {
        Mark();

        switch (Peek()) {
            case ' ':
            case '\t':
            case '\v':
            case '\f':
                Advance();
                ScanWhitespace();
                break;
            case '/':
                switch (Peek(1)) {
                    case '/':
                        Advance(2);
                        ScanLineComment();
                        break;
                    case '*':
                        Advance(2);
                        if (ScanBlockComment())
                            return true;
                        break;
                    default:
                        return false;
                }
                break;
            case '\r':
                Advance();
                Consume('\n');
                AddTrivia(TriviaKind::EndOfLine);
                if (mode != LexingMode::Normal)
                    return true;
                break;
            case '\n':
                Advance();
                AddTrivia(TriviaKind::EndOfLine);
                if (mode != LexingMode::Normal)
                    return true;
                break;
            case '\\':
                // if we're lexing a directive, this might escape a newline
                if (mode == LexingMode::Normal || !IsNewline(Peek()))
                    return false;
                Advance();
                break;
            default:
                return false;
        }
    }
}

void Lexer::ScanWhitespace() {
    bool done = false;
    while (!done) {
        switch (Peek()) {
            case ' ':
            case '\t':
            case '\v':
            case '\f':
                Advance();
                break;
            default:
                done = true;
                break;
        }
    }

    AddTrivia(TriviaKind::Whitespace);
}

void Lexer::ScanLineComment() {
    while (true) {
        char c = Peek();
        if (c == 0 || IsNewline(c))
            break;

        Advance();
    }

    AddTrivia(TriviaKind::LineComment);
}

bool Lexer::ScanBlockComment() {
    bool eod = false;
    while (true) {
        char c = Peek();
        if (c == 0) {
            AddError(DiagCode::UnterminatedBlockComment);
            break;
        }
        else if (c == '*' && Peek(1) == '/') {
            Advance(2);
            break;
        }
        else {
            Advance();
            if (mode != LexingMode::Normal && IsNewline(c)) {
                // found a newline in a block comment inside a directive; this is not allowed
                // we need to stop lexing trivia and issue an EndOfDirective token after this comment
                AddError(DiagCode::SplitBlockCommentInDirective);
                mode = LexingMode::Normal;
                eod = true;
            }
        }
    }

    AddTrivia(TriviaKind::BlockComment);
    return eod;
}

void Lexer::AddTrivia(TriviaKind kind) {
    triviaBuffer.emplace(kind, GetCurrentLexeme());
}

void Lexer::AddError(DiagCode code) {
    // TODO:
}

StringRef Lexer::GetCurrentLexeme() {
    uint32_t length = GetCurrentLexemeLength();
    char* str = copyString(pool, marker, length);
    return StringRef(str, length);
}

} // namespace slang