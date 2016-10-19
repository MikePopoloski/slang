//------------------------------------------------------------------------------
// Lexer.h
// Source file lexer.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>

#include "Buffer.h"
#include "BufferPool.h"
#include "Diagnostics.h"
#include "SourceLocation.h"
#include "StringRef.h"
#include "Token.h"

namespace slang {

class VectorBuilder;
class BumpAllocator;
struct SourceBuffer;

/// The lexer can interpret source characters differently depending on mode.
enum class LexerMode {
	/// Normal lexing mode.
    Normal,

	/// We're inside a directive; end of line turns into EndOfDirective
	/// tokens instead of whitespace.
    Directive,

	/// We're lexing an include file name; we're looking at a special
	/// kind of string that might be delimited by angle brackets.
    IncludeFileName
};

/// The Lexer is responsible for taking source text and chopping it up into tokens.
/// Tokens carry along leading "trivia", which is things like whitespace and comments,
/// so that we can programmatically piece back together what the original file looked like.
///
/// There are also helper methods on this class that handle token manipulation on the
/// character level.
class Lexer {
public:
    Lexer(SourceBuffer buffer, BumpAllocator& alloc, Diagnostics& diagnostics);

	// Not copyable
    Lexer(const Lexer&) = delete;
    Lexer& operator=(const Lexer&) = delete;

    /// Lexes the next token from the source code.
    /// This will never return a null pointer; at the end of the buffer,
    /// an infinite stream of EndOfFile tokens will be generated
    Token lex(LexerMode mode = LexerMode::Normal);

    BufferID getBufferID() const;
    BumpAllocator& getAllocator() { return alloc; }
    Diagnostics& getDiagnostics() { return diagnostics; }

    /// Concatenates two tokens together; used for macro pasting.
    static Token concatenateTokens(BumpAllocator& alloc, Token left, Token right);

    /// Converts a range of tokens into a string literal; used for macro stringification.
    static Token stringify(BumpAllocator& alloc, SourceLocation location, ArrayRef<Trivia> trivia, Token* begin, Token* end);

private:
    Lexer(BufferID bufferId, StringRef source, BumpAllocator& alloc, Diagnostics& diagnostics);

    TokenKind lexToken(Token::Info* info, bool directiveMode);
    TokenKind lexNumericLiteral(Token::Info* info);
    TokenKind lexEscapeSequence(Token::Info* info);
    TokenKind lexDollarSign(Token::Info* info);
    TokenKind lexDirective(Token::Info* info);
    TokenKind lexApostrophe(Token::Info* info);

    Token lexIncludeFileName();

    void lexStringLiteral(Token::Info* info);
    bool lexIntegerBase(Token::Info* info, bool isSigned);
    bool lexTimeLiteral(Token::Info* info);

    bool lexTrivia(Buffer<Trivia>& triviaBuffer, bool directiveMode);
    
    bool scanBlockComment(Buffer<Trivia>& triviaBuffer, bool directiveMode);
    void scanLineComment(Buffer<Trivia>& triviaBuffer, bool directiveMode);
    void scanWhitespace(Buffer<Trivia>& triviaBuffer);
    void scanIdentifier();
    void scanUnsignedNumber(uint64_t& value, int& digits);
    bool scanExponent(uint64_t& value, bool& negative);
    
    void addTrivia(TriviaKind kind, Buffer<Trivia>& triviaBuffer);
    void addError(DiagCode code, uint32_t offset);

    // source pointer manipulation
    void mark() { marker = sourceBuffer; }
    void advance() { sourceBuffer++; }
    void advance(int count) { sourceBuffer += count; }
    char peek() { return *sourceBuffer; }
    char peek(int offset) { return sourceBuffer[offset]; }
    uint32_t currentOffset();

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

    BumpAllocator& alloc;
    Diagnostics& diagnostics;

    // buffer for building string literals
    Buffer<char> stringBuffer;

    // pool of trivia buffers
    BufferPool<Trivia> triviaPool;

    // the source text and start and end pointers within it
    BufferID bufferId;
    const char* originalBegin;
    const char* sourceBuffer;
    const char* sourceEnd;

    // save our place in the buffer to measure out the current lexeme
    const char* marker;
};

}