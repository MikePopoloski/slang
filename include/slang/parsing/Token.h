//------------------------------------------------------------------------------
//! @file Token.h
//! @brief Contains the Token class and related helpers
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/numeric/SVInt.h"
#include "slang/numeric/Time.h"
#include "slang/parsing/TokenKind.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {

class Diagnostics;

namespace syntax {

class SyntaxNode;
enum class SyntaxKind;

} // namespace syntax

} // namespace slang

namespace slang::parsing {

class Token;

/// Various flags for numeric tokens.
struct SLANG_EXPORT NumericTokenFlags {
    uint8_t raw = 0;

    LiteralBase base() const { return LiteralBase(raw & 0b11); }
    bool isSigned() const { return (raw & 0b100) != 0; }
    TimeUnit unit() const { return TimeUnit((raw & 0b111000) >> 3); }
    bool outOfRange() const { return (raw & 0b1000000) != 0; }

    void set(LiteralBase base, bool isSigned);
    void set(TimeUnit unit);
    void setOutOfRange(bool value);
};

/// The Trivia class holds on to a piece of source text that should otherwise
/// not turn into a token; for example, a preprocessor directive, a line continuation
/// character, or a comment.
class SLANG_EXPORT Trivia {
private:
#ifndef __clang_analyzer__
#    pragma pack(push, 4)
#endif
    struct ShortStringView {
        const char* ptr;
        uint32_t len;
    };
    struct ShortTokenSpan {
        const Token* ptr;
        uint32_t len;
    };
    struct FullLocation {
        std::string_view text;
        SourceLocation location;
    };

    union {
        ShortStringView rawText;
        ShortTokenSpan tokens;
        syntax::SyntaxNode* syntaxNode;
        FullLocation* fullLocation;
    };
#ifndef __clang_analyzer__
#    pragma pack(pop)
#endif

    // The vast majority of trivia lives alongside the token it's attached to, so if
    // you want to know its source location just walk backward from the parent location.
    // For certain cases though (the preprocessor inserted tokens) the trivia gets glued
    // together from different locations. In that case hasFullLocation will be true and
    // the union will point at a FullLocation structure.
    bool hasFullLocation = false;

public:
    TriviaKind kind;

    Trivia();
    Trivia(TriviaKind kind, std::string_view rawText);
    Trivia(TriviaKind kind, std::span<Token const> tokens);
    Trivia(TriviaKind kind, syntax::SyntaxNode* syntax);

    bool valid() const { return kind != TriviaKind::Unknown; }

    explicit operator bool() const { return valid(); }

    /// If the trivia is raw source text, creates a new trivia attached from behind
    /// to the specified location (instead of implicitly offset from the parent token).
    /// If this trivia is for a directive or skipped tokens, returns a copy without
    /// modification.
    [[nodiscard]] Trivia withLocation(BumpAllocator& alloc, SourceLocation anchorLocation) const;

    /// Gets the source location of the trivia if one is explicitly known. If not, nullopt
    /// is returned to signify that the location is implicitly relative to the parent token
    /// or subsequent trivia.
    std::optional<SourceLocation> getExplicitLocation() const;

    /// If this trivia is tracking a skipped syntax node or a directive, returns that node.
    /// Otherwise returns nullptr.
    syntax::SyntaxNode* syntax() const;

    /// Get the raw text of the trivia, if any.
    std::string_view getRawText() const;

    /// If the trivia represents skipped tokens, returns the list of tokens that were
    /// skipped. Otherwise returns an empty span.
    std::span<Token const> getSkippedTokens() const;

    Trivia clone(BumpAllocator& alloc, bool deep = false) const;
};
#if !defined(_M_IX86) && !defined(__clang_analyzer__)
static_assert(sizeof(Trivia) == 16);
#endif

/// Represents a single lexed token, including leading trivia, original location, token kind,
/// and any related information derived from the token itself (such as the lexeme).
///
/// This class is a lightweight immutable structure designed to be copied around and stored
/// wherever. The bulk of the token's data is stored in a heap allocated block. Most of the
/// hot path only cares about the token's kind, so that's given priority.
class SLANG_EXPORT Token {
public:
    /// The kind of the token; this is not in the info block because
    /// we almost always want to look at it (perf).
    TokenKind kind;

    Token();
    Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
          std::string_view rawText, SourceLocation location);
    Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
          std::string_view rawText, SourceLocation location, std::string_view strText);
    Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
          std::string_view rawText, SourceLocation location, syntax::SyntaxKind directive);
    Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
          std::string_view rawText, SourceLocation location, logic_t bit);
    Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
          std::string_view rawText, SourceLocation location, const SVInt& value);
    Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
          std::string_view rawText, SourceLocation location, double value, bool outOfRange,
          std::optional<TimeUnit> timeUnit);
    Token(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
          std::string_view rawText, SourceLocation location, LiteralBase base, bool isSigned);

    /// A missing token was expected and inserted by the parser at a given point.
    bool isMissing() const { return missing; }

    SourceRange range() const;
    SourceLocation location() const;
    std::span<Trivia const> trivia() const;

    /// Value text is the "nice" lexed version of certain tokens;
    /// for example, in string literals, escape sequences are converted appropriately.
    std::string_view valueText() const;

    /// Gets the original lexeme that led to the creation of this token.
    std::string_view rawText() const;

    /// Prints the token (including all of its trivia) to a string.
    std::string toString() const;

    /// Data accessors for specific kinds of tokens.
    /// These will generally assert if the kind is wrong.
    SVInt intValue() const;
    double realValue() const;
    logic_t bitValue() const;
    NumericTokenFlags numericFlags() const;
    syntax::SyntaxKind directiveKind() const;

    /// Returns true if this token is on the same line as the token before it.
    /// This is detected by examining the leading trivia of this token for newlines.
    bool isOnSameLine() const;

    bool valid() const { return info != nullptr; }
    explicit operator bool() const { return valid(); }

    bool operator==(const Token& other) const { return kind == other.kind && info == other.info; }

    /// Modification methods to make it easier to deal with immutable tokens.
    [[nodiscard]] Token withTrivia(BumpAllocator& alloc, std::span<Trivia const> trivia) const;
    [[nodiscard]] Token withLocation(BumpAllocator& alloc, SourceLocation location) const;
    [[nodiscard]] Token withRawText(BumpAllocator& alloc, std::string_view rawText) const;
    [[nodiscard]] Token clone(BumpAllocator& alloc, std::span<Trivia const> trivia,
                              std::string_view rawText, SourceLocation location) const;
    [[nodiscard]] Token deepClone(BumpAllocator& alloc) const;

    static Token createMissing(BumpAllocator& alloc, TokenKind kind, SourceLocation location);
    static Token createExpected(BumpAllocator& alloc, Diagnostics& diagnostics, Token actual,
                                TokenKind expected, Token lastConsumed, Token matchingDelim);

private:
    struct Info;

    void init(BumpAllocator& alloc, TokenKind kind, std::span<Trivia const> trivia,
              std::string_view rawText, SourceLocation location);

    // Some data is stored directly in the token here because we have 6 bytes of padding that
    // would otherwise go unused. The rest is stored in the info block.
    bool missing : 1;
    uint8_t triviaCountSmall : 4;
    uint8_t reserved : 3;
    NumericTokenFlags numFlags;
    uint32_t rawLen = 0;
    Info* info = nullptr;

    // We use some free bits in the token structure to count how many trivia elements
    // this token has. This is enough space for the vast majority of tokens, but for
    // cases with more, triviaCountSmall gets set to all 1's and the real count is
    // included in the info structure.
    static constexpr int MaxTriviaSmallCount = (1 << 4) - 2;
};

#if !defined(_M_IX86)
static_assert(sizeof(Token) == 16);
#endif
static_assert(std::is_trivially_copyable_v<Token>);

} // namespace slang::parsing
