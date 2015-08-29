#pragma once

namespace slang {

// TODO:
// - scan directives
// - numeric literals

class Lexer {
public:
    Lexer(const char* sourceBuffer, Allocator& pool, Diagnostics& diagnostics);

    Token* lex();

private:
    TokenKind lexToken(void** extraData);
    TokenKind lexNumericLiteral(void** extraData);
    TokenKind lexEscapeSequence(void** extraData);
    TokenKind lexDollarSign(void** extraData);
    TokenKind lexDirective(void** extraData);
    void scanStringLiteral(void** extraData);
    void scanUnsizedNumericLiteral(void** extraData);
    void scanVectorLiteral(void** extraData);
    void scanIdentifier();
    void scanExponent();

    bool lexTrivia();
    bool scanBlockComment();
    void scanWhitespace();
    void scanLineComment();

    // factory helper methods
    void addTrivia(TriviaKind kind);
    void addError(DiagCode code);

    // source pointer manipulation
    void mark() { marker = sourceBuffer; }
    void advance() { sourceBuffer++; }
    void advance(int count) { sourceBuffer += count; }
    char peek() { return *sourceBuffer; }
    char peek(int offset) { return sourceBuffer[offset]; }

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
    Allocator& pool;
    Diagnostics& diagnostics;
    const char* sourceBuffer;
    const char* marker;
    LexingMode mode;
};

}