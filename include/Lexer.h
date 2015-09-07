#pragma once

namespace slang {

class Lexer {
public:
    Lexer(FileID file, StringRef source, BumpAllocator& alloc, Diagnostics& diagnostics);

    Lexer(const Lexer&) = delete;
    Lexer& operator=(const Lexer&) = delete;

    Token* lex();

    FileID getFile() const { return file; }
    BumpAllocator& getAllocator() const { return alloc; }
    Diagnostics& getDiagnostics() const { return diagnostics; }

private:
    TokenKind lexToken(void** extraData);
    TokenKind lexNumericLiteral(void** extraData);
    TokenKind lexEscapeSequence(void** extraData);
    TokenKind lexDollarSign(void** extraData);
    TokenKind lexDirective(void** extraData);
    char scanUnsignedNumber(char c, uint64_t& unsignedVal, int& digits);
    void scanIdentifier();

    StringLiteralInfo* lexStringLiteral();
    StringLiteralInfo* lexIncludeFileName(char delim);
    NumericLiteralInfo* lexRealLiteral(uint64_t value, int decPoint, int digits, bool exponent);
    NumericLiteralInfo* lexVectorLiteral(uint64_t size);
    NumericLiteralInfo* lexUnsizedNumericLiteral();

    template<bool (*IsDigitFunc)(char), uint32_t (*ValueFunc)(char)>
    NumericLiteralInfo* lexVectorDigits();

    bool lexTrivia();
    bool scanBlockComment();
    void scanWhitespace();
    void scanLineComment();

    int findNextNonWhitespace();

    // factory helper methods
    void addTrivia(TriviaKind kind);
    void addError(DiagCode code);

    // source pointer manipulation
    void mark() { marker = sourceBuffer; }
    void advance() { sourceBuffer++; }
    void advance(int count) { sourceBuffer += count; }
    char peek() { return *sourceBuffer; }
    char peek(int offset) { return sourceBuffer[offset]; }

    // in order to detect embedded nulls gracefully, we call this whenever we
    // encounter a null to check whether we really are at the end of the buffer
    bool reallyAtEnd() { return sourceBuffer >= sourceEnd; }

    uint32_t lexemeLength() { return (uint32_t)(sourceBuffer - marker); }
    StringRef lexeme();

    bool consume(char c) {
        if (peek() == c) {
            advance();
            return true;
        }
        return false;
    }

    enum class LexingMode {
        Normal,
        Include,
        Directive
    };

    Buffer<char> stringBuffer;
    Buffer<Trivia> triviaBuffer;
    VectorBuilder vectorBuilder;

    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    const char* sourceBuffer;
    const char* sourceEnd;
    const char* marker;
    FileID file;
    LexingMode mode;
};

}