//------------------------------------------------------------------------------
// Trivia.h
// Support for tracking trivia like whitespace and comments.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>

#include "ArrayRef.h"
#include "Buffer.h"
#include "StringRef.h"

namespace slang {

class Token;
class SyntaxNode;

/// The kind of trivia we've stored.
enum class TriviaKind : uint8_t {
    Unknown,
    Whitespace,
    EndOfLine,
    LineContinuation,
    LineComment,
    BlockComment,
    DisabledText,
    SkippedTokens,
    SkippedSyntax,
    Directive
};

/// The Trivia class holds on to a piece of source text that should otherwise
/// not turn into a token; for example, a preprocessor directive, a line continuation
/// character, or a comment.
class Trivia {
public:
    TriviaKind kind;

    Trivia() : kind(TriviaKind::Unknown), rawText(nullptr) {}
    Trivia(TriviaKind kind, StringRef rawText) : kind(kind), rawText(rawText) {}
    Trivia(TriviaKind kind, ArrayRef<Token> tokens) : kind(kind), tokens(tokens) {}
    Trivia(TriviaKind kind, SyntaxNode* syntax) : kind(kind), syntaxNode(syntax) {}

    /// Writes the trivia's text to the given buffer.
    void writeTo(Buffer<char>& buffer, uint8_t flags = 0) const;

    /// If this trivia is tracking a skipped syntax node, return that now.
    SyntaxNode* syntax() const;

private:
    union {
        StringRef rawText;
        ArrayRef<Token> tokens;
        SyntaxNode* syntaxNode;
    };
};

}