//------------------------------------------------------------------------------
//! @file Lexer.h
//! @brief Source file lexer
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/Diagnostics.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/parsing/Token.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Hash.h"
#include "slang/util/LanguageVersion.h"
#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {

class BumpAllocator;
class SourceManager;

} // namespace slang

namespace slang::parsing {

/// A handler for a specific kind of directive embedded in comments in the
/// user source text.
struct CommentHandler {
    /// The kind of directive this handler is for.
    enum Kind {
        /// A region that should be skipped (as if it were a pragma protect region).
        Protect,

        /// A region that should be skipped (as if it were commented out).
        TranslateOff,

        /// Turns linting on for one or more warnings.
        LintOn,

        /// Turns linting off for one or more warnings.
        LintOff,

        /// Saves the current lint state in a stack.
        LintSave,

        /// Restore a previously set lint state.
        LintRestore
    };

    /// The kind of comment handler this is.
    Kind kind;

    /// For region handler, the text that marks the end of the region.
    std::string_view endRegion;

    CommentHandler() = default;
    CommentHandler(Kind kind, std::string_view endRegion = {}) : kind(kind), endRegion(endRegion) {}
};

using CommentHandlerMap =
    flat_hash_map<std::string_view, flat_hash_map<std::string_view, CommentHandler>>;

/// Contains various options that can control lexing behavior.
struct SLANG_EXPORT LexerOptions {
    /// A map of comment handlers to use when lexing directives inside comments.
    CommentHandlerMap commentHandlers;

    /// The maximum number of errors that can occur before the rest of the source
    /// buffer is skipped.
    uint32_t maxErrors = 16;

    /// The version of the SystemVerilog language to use.
    LanguageVersion languageVersion = LanguageVersion::Default;

    /// If true, the preprocessor will support legacy protected envelope directives,
    /// for compatibility with old Verilog tools.
    bool enableLegacyProtect = false;
};

/// Possible encodings for encrypted text used in a pragma protect region.
enum class SLANG_EXPORT ProtectEncoding { UUEncode, Base64, QuotedPrintable, Raw };

/// The Lexer is responsible for taking source text and chopping it up into tokens.
/// Tokens carry along leading "trivia", which is things like whitespace and comments,
/// so that we can programmatically piece back together what the original file looked like.
///
/// There are also helper methods on this class that handle token manipulation on the
/// character level.
class SLANG_EXPORT Lexer {
public:
    Lexer(SourceBuffer buffer, BumpAllocator& alloc, Diagnostics& diagnostics,
          SourceManager& sourceManager, LexerOptions options = LexerOptions{});

    // Not copyable
    Lexer(const Lexer&) = delete;
    Lexer& operator=(const Lexer&) = delete;

    /// Lexes the next token from the source code.
    /// This will never return a null pointer; at the end of the buffer,
    /// an infinite stream of EndOfFile tokens will be generated
    Token lex();
    Token lex(KeywordVersion keywordVersion);

    /// Looks ahead in the source stream to see if the next token we would lex
    /// is on the same line as the previous token we've lexed.
    bool isNextTokenOnSameLine();

    /// Lexes a token that contains encoded text as part of a protected envelope.
    Token lexEncodedText(ProtectEncoding encoding, uint32_t expectedBytes, bool singleLine,
                         bool legacyProtectedMode);

    /// Returns the library with which the lexer's source buffer is associated.
    const SourceLibrary* getLibrary() const { return library; }

    /// Concatenates two tokens together; used for macro pasting.
    static Token concatenateTokens(BumpAllocator& alloc, SourceManager& sourceManager, Token left,
                                   Token right);

    /// Converts a range of tokens into a string literal; used for macro stringification.
    static Token stringify(Lexer& parentLexer, Token startToken, std::span<Token> bodyTokens,
                           Token endToken);

    /// Converts a range of tokens into a block comment; used for macro expansion.
    static Trivia commentify(BumpAllocator& alloc, SourceManager& sourceManager,
                             std::span<Token> tokens);

    /// Splits the given token at the specified offset into its raw source text. The trailing
    /// portion of the split is lexed into new tokens and appened to @a results
    static void splitTokens(BumpAllocator& alloc, Diagnostics& diagnostics,
                            SourceManager& sourceManager, Token sourceToken, size_t offset,
                            KeywordVersion keywordVersion, SmallVectorBase<Token>& results);

private:
    Lexer(BufferID bufferId, std::string_view source, const char* startPtr, BumpAllocator& alloc,
          Diagnostics& diagnostics, SourceManager& sourceManager, LexerOptions options);

    Token lexToken(KeywordVersion keywordVersion);
    Token lexEscapeSequence(bool isMacroName);
    Token lexNumericLiteral();
    Token lexDollarSign();
    Token lexDirective();
    Token lexApostrophe();

    Token lexStringLiteral();
    std::optional<TimeUnit> lexTimeLiteral();

    template<bool StopAfterNewline>
    void lexTrivia();

    void scanBlockComment();
    void scanLineComment();
    void scanWhitespace();
    void scanIdentifier();
    bool scanUTF8Char(bool alreadyErrored);
    bool scanUTF8Char(bool alreadyErrored, uint32_t* code, int& computedLen);
    void scanEncodedText(ProtectEncoding encoding, uint32_t expectedBytes, bool singleLine,
                         bool legacyProtectedMode);
    bool tryApplyCommentHandler();
    void scanDisabledRegion(std::string_view firstWord, std::string_view secondWord,
                            std::optional<std::string_view> thirdWord, DiagCode unclosedDiag);

    template<typename... Args>
    Token create(TokenKind kind, Args&&... args);

    void addTrivia(TriviaKind kind);
    Diagnostic& addDiag(DiagCode code, size_t offset);

    // source pointer manipulation
    void mark() { marker = sourceBuffer; }
    void advance() { sourceBuffer++; }
    void advance(int count) { sourceBuffer += count; }
    char peek() const { return *sourceBuffer; }
    char peek(int offset) const { return sourceBuffer[offset]; }
    size_t currentOffset() const;

    // in order to detect embedded nulls gracefully, we call this whenever we
    // encounter a null to check whether we really are at the end of the buffer
    bool reallyAtEnd() const { return sourceBuffer >= sourceEnd - 1; }

    uint32_t lexemeLength() const { return (uint32_t)(sourceBuffer - marker); }
    std::string_view lexeme() const { return std::string_view(marker, lexemeLength()); }

    bool consume(char c) {
        if (peek() == c) {
            advance();
            return true;
        }
        return false;
    }

    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    LexerOptions options;

    // the source text and start and end pointers within it
    BufferID bufferId;
    const char* originalBegin;
    const char* sourceBuffer;
    const char* sourceEnd;

    // save our place in the buffer to measure out the current lexeme
    const char* marker;

    // the number of errors that have occurred while lexing the current buffer
    uint32_t errorCount = 0;

    // temporary storage for building arrays of trivia
    SmallVector<Trivia, 32> triviaBuffer;

    // temporary storage for building string literals
    SmallVector<char> stringBuffer;

    const SourceLibrary* library = nullptr;
    SourceManager& sourceManager;
};

} // namespace slang::parsing
