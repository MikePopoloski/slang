//------------------------------------------------------------------------------
//! @file Token.h
//! @brief Contains the Token class and related helpers
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <array>
#include <ranges>

#include "slang/numeric/SVInt.h"
#include "slang/numeric/Time.h"
#include "slang/parsing/KnownSystemName.h"
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

/// A lightweight view over a sequence of Trivia objects associated with a Token.
///
/// Most of the time the view simply wraps an externally stored contiguous buffer
/// of Trivia (i.e. the buffer that lives in a Token's heap-allocated info block).
/// However, certain very common single-trivia cases (a short whitespace run or a
/// newline) are encoded directly into free bits of the parent Token, in which
/// case the view materializes a synthesized Trivia on the fly. That synthesized
/// Trivia is stored inside the view itself so iteration can return references
/// into the view's own storage.
///
/// This type models `std::ranges::view` so it can be used with the standard
/// ranges library (e.g. piped through `std::views::filter`). Iterators returned
/// by `begin()`/`end()` reference the view object itself; do not move or destroy
/// the view while iterators into it are still in use.
class SLANG_EXPORT TriviaView : public std::ranges::view_interface<TriviaView> {
public:
    using value_type = Trivia;
    using element_type = const Trivia;
    using size_type = size_t;
    using difference_type = std::ptrdiff_t;

    /// Constructs an empty view.
    TriviaView() noexcept = default;

    /// Constructs a view over an externally stored contiguous range of Trivia.
    template<std::ranges::contiguous_range R>
        requires std::same_as<std::remove_cvref_t<std::ranges::range_value_t<R>>, Trivia> &&
                     (!std::same_as<std::remove_cvref_t<R>, TriviaView>)
    TriviaView(R&& range) noexcept :
        externPtr(std::ranges::data(range)), count(std::ranges::size(range)) {}

    /// Constructs a view from a span of Trivia.
    TriviaView(std::span<const Trivia> span) noexcept :
        externPtr(span.data()), count(span.size()) {}

    /// Copy/move constructors fix up the inline storage pointer for views that
    /// hold a synthesized Trivia.
    TriviaView(const TriviaView& other) noexcept { copyFrom(other); }
    TriviaView(TriviaView&& other) noexcept { copyFrom(other); }
    TriviaView& operator=(const TriviaView& other) noexcept {
        if (this != &other)
            copyFrom(other);
        return *this;
    }
    TriviaView& operator=(TriviaView&& other) noexcept {
        if (this != &other)
            copyFrom(other);
        return *this;
    }

    /// Constructs a view containing one or two inline Trivia. The trivia are
    /// held by value inside the view; iterators reference them directly.
    static TriviaView makeInline(const Trivia* src, size_t n) noexcept {
        SLANG_ASSERT(n >= 1 && n <= 2);
        TriviaView v;
        for (size_t i = 0; i < n; ++i)
            v.inlineStorage[i] = src[i];
        v.externPtr = nullptr;
        v.count = n;
        return v;
    }

    /// Number of Trivia elements in the view.
    size_t size() const noexcept { return count; }

    /// True if the view is empty.
    bool empty() const noexcept { return count == 0; }

    /// Pointer to the underlying contiguous buffer. For inline views this points
    /// at the view's internal storage; for external views it points at the
    /// originally referenced buffer. Only valid while the view is alive.
    const Trivia* data() const noexcept { return externPtr ? externPtr : inlineStorage.data(); }

    const Trivia& operator[](size_t i) const noexcept {
        SLANG_ASSERT(i < count);
        return data()[i];
    }

    const Trivia& front() const noexcept { return (*this)[0]; }
    const Trivia& back() const noexcept { return (*this)[count - 1]; }

    using iterator = const Trivia*;
    using const_iterator = const Trivia*;
    using reverse_iterator = std::reverse_iterator<iterator>;
    using const_reverse_iterator = std::reverse_iterator<const_iterator>;

    iterator begin() const noexcept { return data(); }
    iterator end() const noexcept { return data() + count; }
    reverse_iterator rbegin() const noexcept { return reverse_iterator(end()); }
    reverse_iterator rend() const noexcept { return reverse_iterator(begin()); }

private:
    void copyFrom(const TriviaView& other) noexcept {
        if (other.externPtr) {
            externPtr = other.externPtr;
        }
        else {
            inlineStorage = other.inlineStorage;
            externPtr = nullptr;
        }
        count = other.count;
    }

    // When externPtr is non-null, the view aliases an external buffer of `count` Trivia.
    // When externPtr is null and count > 0, `inlineStorage` holds the trivia.
    // When count == 0, the view is empty (both pointer and storage are unused).
    const Trivia* externPtr = nullptr;
    size_t count = 0;
    std::array<Trivia, 2> inlineStorage;
};

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
    Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia, std::string_view rawText,
          SourceLocation location);
    Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia, std::string_view rawText,
          SourceLocation location, std::string_view strText);
    Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia, std::string_view rawText,
          SourceLocation location, syntax::SyntaxKind directive);
    Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia, std::string_view rawText,
          SourceLocation location, KnownSystemName systemName);
    Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia, std::string_view rawText,
          SourceLocation location, logic_t bit);
    Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia, std::string_view rawText,
          SourceLocation location, const SVInt& value);
    Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia, std::string_view rawText,
          SourceLocation location, double value, bool outOfRange, std::optional<TimeUnit> timeUnit);
    Token(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia, std::string_view rawText,
          SourceLocation location, LiteralBase base, bool isSigned);

    /// A missing token was expected and inserted by the parser at a given point.
    bool isMissing() const { return missing; }

    SourceRange range() const;
    SourceLocation location() const;
    TriviaView trivia() const;

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
    KnownSystemName systemName() const;

    /// Returns true if this token is on the same line as the token before it.
    /// This is detected by examining the leading trivia of this token for newlines.
    bool isOnSameLine() const;

    /// Returns true if this token's trivia (if any) is encoded inline within
    /// the token's own bits, requiring no separate allocation in the info block.
    bool hasInlinedTrivia() const { return hasInlineTrivia; }

    /// Gets the number of bytes in the info block used to store this token's
    /// trivia, including any overflow count header. Returns 0 when the trivia
    /// is empty or encoded inline.
    size_t getTriviaSizeInBytes() const;

    /// Gets the allocated size of this token, in bytes, including its trivia.
    size_t getSizeInBytes() const;

    bool valid() const { return hasInfoPtr || kind != TokenKind::Unknown; }
    explicit operator bool() const { return valid(); }

    bool operator==(const Token& other) const {
        if (kind != other.kind)
            return false;
        if (hasInlineTrivia != other.hasInlineTrivia)
            return false;
        if (hasInlineTrivia && triviaCountSmall != other.triviaCountSmall)
            return false;
        return hasInfoPtr ? info == other.info : nonInfoLoc == other.nonInfoLoc;
    }

    /// Modification methods to make it easier to deal with immutable tokens.
    [[nodiscard]] Token withTrivia(BumpAllocator& alloc, const TriviaView& trivia) const;
    [[nodiscard]] Token withLocation(BumpAllocator& alloc, SourceLocation location) const;
    [[nodiscard]] Token withRawText(BumpAllocator& alloc, std::string_view rawText) const;
    [[nodiscard]] Token clone(BumpAllocator& alloc, const TriviaView& trivia,
                              std::string_view rawText, SourceLocation location) const;
    [[nodiscard]] Token deepClone(BumpAllocator& alloc) const;

    static Token createMissing(BumpAllocator& alloc, TokenKind kind, SourceLocation location);
    static Token createExpected(BumpAllocator& alloc, Diagnostics& diagnostics, Token actual,
                                TokenKind expected, Token lastConsumed, Token matchingDelim);

    /// Returns true if the bytes at @a storage (which must be at least
    /// sizeof(Token) bytes) appear to contain a Token (rather than a pointer).
    static bool storageHasTokenTag(const void* storage) {
        uint32_t marker;
        std::memcpy(&marker, static_cast<const std::byte*>(storage) + RawLenAndExtraOffset,
                    sizeof(marker));
        return (marker & TokenTag) != 0;
    }

private:
    struct Info;

    void init(BumpAllocator& alloc, TokenKind kind, const TriviaView& trivia,
              std::string_view rawText, SourceLocation location);

    Info& getInfo() const {
        SLANG_ASSERT(hasInfoPtr && info);
        return *info;
    }

    // Some data is stored directly in the token here because we have 6 bytes of padding that
    // would otherwise go unused. The rest is stored in the info block.
    bool missing : 1;
    bool hasInfoPtr : 1;

    // When set, the token has 1 or 2 trivia elements encoded directly into
    // `triviaCountSmall` (interpreted as an inline-trivia code) rather than
    // stored in the info block.
    bool hasInlineTrivia : 1;

    // When `hasInlineTrivia` is false: a small count of trivia elements stored
    // in the info block (0 means no trivia; values 1..MaxTriviaSmallCount give
    // the count directly; MaxTriviaSmallCount+1 is the overflow indicator that
    // means the real count is stored in the info block).
    //
    // When `hasInlineTrivia` is true: a 5-bit code identifying the inline
    // trivia (one or two elements). See encodeInlineTrivia/decodeInlineTrivia.
    uint8_t triviaCountSmall : 5;

    NumericTokenFlags numFlags;

    // This is the length of the raw text string, stored in the Info block,
    // if we have one. Also for some kinds we pack some data into bits 16-30.
    // We know in those cases that the raw length can't possibly be long
    // enough to need those extra bits. The top bit (TokenTag) is always set
    // on a valid Token; it is reserved so that a Token can be distinguished
    // from a pointer when both are stored in the same union
    // (see syntax::ConstTokenOrSyntax).
    uint32_t rawLenAndExtra = TokenTag;

    // Tokens have an info block unless they have no trivia, no raw text,
    // and no other extra info to carry. In that case we just store the
    // location here and don't allocate an info block.
    union {
        Info* info = nullptr;
        SourceLocation nonInfoLoc;
    };

    // We use some free bits in the token structure to count how many trivia elements
    // this token has. This is enough space for the vast majority of tokens, but for
    // cases with more, triviaCountSmall gets set to all 1's and the real count is
    // included in the info structure.
    static constexpr int MaxTriviaSmallCount = (1 << 5) - 2;

    // Reserved bit pattern in rawLenAndExtra that is always set on a
    // constructed Token. This allows a Token to be distinguished from a
    // pointer when both occupy the same memory in a union.
    static constexpr uint32_t TokenTag = 0x80000000u;

    // Byte offset of the rawLenAndExtra field within Token. The actual
    // field offset is verified to equal this constant via a runtime
    // assertion in init().
    static constexpr size_t RawLenAndExtraOffset = 4;
};

static_assert(std::is_trivially_copyable_v<Token>);

} // namespace slang::parsing
