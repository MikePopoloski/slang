#pragma once

namespace slang {

enum class LexerMode {
    Normal,
    Directive,
    IncludeFileName
};

class Lexer {
public:
    Lexer(const SourceBuffer* buffer, BumpAllocator& alloc, Diagnostics& diagnostics);

    Lexer(const Lexer&) = delete;
    Lexer& operator=(const Lexer&) = delete;

    // lex the next token from the source code
    // will never return a null pointer; at the end of the buffer,
    // an infinite stream of EndOfFile tokens will be generated
    Token* lex(LexerMode mode = LexerMode::Normal);

    FileID getFile() const { return file; }
    BumpAllocator& getAllocator() { return alloc; }
    Diagnostics& getDiagnostics() { return diagnostics; }

private:
    struct TokenInfo {
        StringRef niceText;
        NumericValue numericValue;
        SyntaxKind directiveKind = SyntaxKind::Unknown;
        IdentifierType identifierType = IdentifierType::Unknown;
        uint32_t offset = 0;
        uint8_t numericFlags = 0;
    };

    TokenKind lexToken(TokenInfo& info, bool directiveMode);
    TokenKind lexNumericLiteral(TokenInfo& info);
    TokenKind lexEscapeSequence(TokenInfo& info);
    TokenKind lexDollarSign(TokenInfo& info);
    TokenKind lexDirective(TokenInfo& info);
    TokenKind lexApostrophe(TokenInfo& info);

    Token* lexIncludeFileName();

    void lexStringLiteral(TokenInfo& info);
    bool lexIntegerBase(TokenInfo& info);
    bool lexTimeLiteral(TokenInfo& info);

    bool lexTrivia(Buffer<Trivia>& buffer, bool directiveMode);
    
    bool scanBlockComment(Buffer<Trivia>& buffer, bool directiveMode);
    void scanWhitespace(Buffer<Trivia>& buffer);
    void scanLineComment(Buffer<Trivia>& buffer);
    void scanIdentifier();
    void scanUnsignedNumber(uint64_t& value, int& digits);
    bool scanExponent(uint64_t& value, bool& negative);

    Token* createToken(TokenKind kind, TokenInfo& info, Buffer<Trivia>& triviaBuffer);
    void addTrivia(TriviaKind kind, Buffer<Trivia>& buffer);
    void addError(DiagCode code, uint32_t offset);

    // source pointer manipulation
    void mark() { marker = sourceBuffer; }
    void advance() { sourceBuffer++; }
    void advance(int count) { sourceBuffer += count; }
    char peek() { return *sourceBuffer; }
    char peek(int offset) { return sourceBuffer[offset]; }
    uint32_t currentOffset() { return (uint32_t)(sourceBuffer - startPointer); }

    // in order to detect embedded nulls gracefully, we call this whenever we
    // encounter a null to check whether we really are at the end of the buffer
    bool reallyAtEnd() { return sourceBuffer >= sourceEnd - 1; }

    uint32_t lexemeLength() { return (uint32_t)(sourceBuffer - marker); }
    StringRef lexeme() { return StringRef(marker, lexemeLength()); }

    bool consume(char c) {
        if (peek() == c) {
            advance();
            return true;
        }
        return false;
    }

    Buffer<char> stringBuffer;
    BufferPool<Trivia> triviaPool;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    const char* const startPointer;
    const char* sourceBuffer;
    const char* sourceEnd;
    const char* marker;
    FileID file;
};

}