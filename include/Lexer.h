#pragma once

namespace slang {

// TODO:
// - string escape sequences
// - track errors
// - populate token
// - scan directives
// - numeric literals

class Lexer {
public:
    Lexer(const char* sourceBuffer, Allocator& pool);

    Token* Lex();

private:
    TokenKind LexToken(void** extraData);
    void ScanIdentifier();
    void ScanExponent();
    void ScanStringLiteral(void** extraData);
    void ScanUnsizedNumericLiteral(void** extraData);
    void ScanVectorLiteral(void** extraData);
    TokenKind ScanNumericLiteral(void** extraData);
    TokenKind ScanEscapeSequence(void** extraData);
    TokenKind ScanDollarSign(void** extraData);
    TokenKind ScanDirective(void** extraData);

    bool LexTrivia();
    bool ScanBlockComment();
    void ScanWhitespace();
    void ScanLineComment();

    // factory helper methods
    void AddTrivia(TriviaKind kind);
    void AddError(DiagCode code);

    // source pointer manipulation
    void Mark() { marker = sourceBuffer; }
    void Advance() { sourceBuffer++; }
    void Advance(int count) { sourceBuffer += count; }
    void Back() { sourceBuffer--; }
    char Next() { return *sourceBuffer++; }
    char Peek() { return *sourceBuffer; }
    char Peek(int offset) { return sourceBuffer[offset]; }

    uint32_t GetCurrentLexemeLength() const { return (uint32_t)(sourceBuffer - marker); }
    StringRef GetCurrentLexeme();
    
    bool Consume(char c) {
        if (Peek() == c) {
            Advance();
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

    Buffer<Trivia> triviaBuffer;
    Buffer<char> stringBuffer;
    Allocator& pool;
    const char* sourceBuffer;
    const char* marker;
    LexingMode mode;
};

}