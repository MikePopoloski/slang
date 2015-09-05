#pragma once

namespace slang {

// TODO:
// - vector values
// - token locations
// - diagnostic locations
// - start of line / flags

class Lexer {
public:
    Lexer(FileID file, StringRef source, Allocator& alloc, Preprocessor& preprocessor, Diagnostics& diagnostics);

    Token* lex();

private:
    TokenKind lexToken(void** extraData);
    TokenKind lexNumericLiteral(void** extraData);
    TokenKind lexEscapeSequence(void** extraData);
    TokenKind lexDollarSign(void** extraData);
    TokenKind lexDirective(void** extraData);
    char scanUnsignedNumber(char c, uint64_t& unsignedVal, int& digits);
    void scanIdentifier();

    StringLiteralInfo* scanStringLiteral();
    NumericLiteralInfo* scanRealLiteral(uint64_t value, int decPoint, int digits, bool exponent);
    NumericLiteralInfo* scanVectorLiteral(uint64_t size);
    NumericLiteralInfo* scanUnsizedNumericLiteral();
    NumericLiteralInfo* scanDecimalVector();
    NumericLiteralInfo* scanOctalVector();
    NumericLiteralInfo* scanHexVector();
    NumericLiteralInfo* scanBinaryVector();

    bool lexTrivia();
    bool scanBlockComment();
    void scanWhitespace();
    void scanLineComment();

    void lexDirectiveTrivia();
    void lexIncludeDirective();

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
        MacroDefine,
        OtherDirective
    };

    Buffer<char> stringBuffer;
    Buffer<Trivia> triviaBuffer;
    VectorBuilder vectorBuilder;
    Allocator& alloc;
    Preprocessor& preprocessor;
    Diagnostics& diagnostics;
    const char* sourceBuffer;
    const char* sourceEnd;
    const char* marker;
    FileID file;
    LexingMode mode;
};

}