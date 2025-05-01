//------------------------------------------------------------------------------
//! @file ParserBase.h
//! @brief Base class for parsing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/Diagnostics.h"
#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxFacts.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/SmallVector.h"

namespace slang::parsing {

class Preprocessor;

/// Base class for the Parser, which contains helpers and language-agnostic parsing routines.
/// Mostly this helps keep the main Parser smaller and more focused.
class SLANG_EXPORT ParserBase {
protected:
    ParserBase(Preprocessor& preprocessor);

    Diagnostics& getDiagnostics();
    Diagnostic& addDiag(DiagCode code, SourceLocation location);
    Diagnostic& addDiag(DiagCode code, SourceRange range);

    // Helper methods to manipulate the underlying token stream.
    Token peek(uint32_t offset);
    Token peek();
    bool peek(TokenKind kind);
    Token consume();
    Token consumeIf(TokenKind kind);
    Token expect(TokenKind kind);
    void skipToken(std::optional<DiagCode> diagCode);
    void pushTokens(std::span<const Token> tokens);

    Token missingToken(TokenKind kind, SourceLocation location);
    Token placeholderToken();

    Token getLastConsumed() const;
    bool haveDiagAtCurrentLoc();

    const std::pair<Token, Token>& getLastPoppedDelims() const { return lastPoppedDelims; }

    Preprocessor& getPP() { return window.tokenSource; }

    /// Helper class that maintains a sliding window of tokens, with lookahead.
    class Window {
    public:
        explicit Window(Preprocessor& source) : tokenSource(source) {
            capacity = 32;
            buffer = new Token[capacity];
        }

        ~Window() { delete[] buffer; }

        // not copyable
        Window(const Window&) = delete;
        Window& operator=(const Window&) = delete;

        // the source of all tokens
        Preprocessor& tokenSource;

        // a buffer of tokens for implementing lookahead
        Token* buffer = nullptr;

        // the current token we're looking at
        Token currentToken;

        // the last token we consumed
        Token lastConsumed;

        // the current offset within the lookahead buffer
        size_t currentOffset = 0;
        size_t count = 0;
        size_t capacity = 0;

        void addNew();
        void moveToNext();
        void insertHead(std::span<const Token> tokens);
    };

    BumpAllocator& alloc;

    /// Generalized helper method for parsing a group of things that are bookended by
    /// known token kinds. The point of wrapping it in a function is that if the starting
    /// token is missing, we don't even bother trying to parse the rest of the group.
    template<typename TParserFunc,
             typename TResult = decltype(std::declval<typename std::decay<TParserFunc>::type&>()())>
    std::tuple<Token, Token, TResult> parseGroupOrSkip(TokenKind startKind, TokenKind endKind,
                                                       TParserFunc&& parseItem) {
        Token start = expect(startKind);
        if (start.isMissing())
            return std::make_tuple(start, missingToken(endKind, start.location()), nullptr);

        TResult result = nullptr;
        if (!peek(endKind))
            result = parseItem();

        Token end = expect(endKind);
        return std::make_tuple(start, end, result);
    }

    enum class AllowEmpty { False, True };
    enum class RequireItems { False, True };

    /// This is a generalized method for parsing a delimiter separated list of things
    /// with bookend tokens in a way that robustly handles bad tokens.
    template<bool (*IsExpected)(TokenKind), bool (*IsEnd)(TokenKind), typename TParserFunc>
    void parseList(TokenKind openKind, TokenKind closeKind, TokenKind separatorKind,
                   Token& openToken, std::span<syntax::TokenOrSyntax>& list, Token& closeToken,
                   RequireItems requireItems, DiagCode code, TParserFunc&& parseItem,
                   AllowEmpty allowEmpty = {}) {
        openToken = expect(openKind);
        if (openToken.isMissing()) {
            closeToken = missingToken(closeKind, openToken.location());
            list = std::span<syntax::TokenOrSyntax>();
            return;
        }

        SmallVector<syntax::TokenOrSyntax, 16> buffer;
        parseList<IsExpected, IsEnd, TParserFunc>(buffer, closeKind, separatorKind, closeToken,
                                                  requireItems, code,
                                                  std::forward<TParserFunc>(parseItem), allowEmpty);
        list = buffer.copy(alloc);
    }

    template<bool (*IsExpected)(TokenKind), bool (*IsEnd)(TokenKind), typename TParserFunc>
    void parseList(SmallVectorBase<syntax::TokenOrSyntax>& buffer, TokenKind closeKind,
                   TokenKind separatorKind, Token& closeToken, RequireItems requireItems,
                   DiagCode code, TParserFunc&& parseItem, AllowEmpty allowEmpty = {}) {
        auto current = peek();
        if (IsEnd(current.kind)) {
            if (requireItems == RequireItems::True && !haveDiagAtCurrentLoc())
                addDiag(code, current.location());

            closeToken = expect(closeKind);
            return;
        }

        // If the very first token isn't expected just bail out of list parsing.
        if (!IsExpected(current.kind)) {
            reportMissingList(current, closeKind, closeToken, code);
            return;
        }

        // Heads up: the ordering of events in this loop can be pretty subtle.
        // Be careful when changing it.
        while (true) {
            // Parse the next item in the list.
            buffer.push_back(parseItem());

            // If we found the end token, we're done with list processing.
            auto next = peek();
            if (IsEnd(next.kind) || next.kind == TokenKind::EndOfFile)
                break;

            // Since the list hasn't ended, we must see a separator here.
            // If we don't, something is wrong and we need to try to recover
            // by skipping tokens until we get back to a separator or end token.
            if (next.kind != separatorKind) {
                // Special case for semicolon-ended lists: we assume that
                // a missing separator means they actually probably missed
                // the *end* token (i.e. the semicolon) and that we'll more
                // easily recover by stopping list processing and letting
                // the calling code move on.
                if (closeKind == TokenKind::Semicolon)
                    break;

                // Otherwise keep sucking up spans of unexpected tokens until
                // we find a separator, our end token, or something that makes
                // us abort completely. We call expect() here to get a diagnostic
                // issued, we know it won't ever return a real token.
                expect(separatorKind);
                do {
                    if (!skipBadTokens<IsExpected, IsEnd>(code, false)) {
                        closeToken = expect(closeKind);
                        return;
                    }
                } while (!peek(separatorKind));
            }

            buffer.push_back(expect(separatorKind));

            next = peek();
            if (IsEnd(next.kind) || next.kind == TokenKind::EndOfFile) {
                if (allowEmpty == AllowEmpty::True) {
                    // Empty items are allowed, so call the parse function
                    // to get one here and then we're finished.
                    buffer.push_back(parseItem());
                }
                else {
                    // Specific check for misplaced trailing separators here.
                    reportMisplacedSeparator();
                }
                break;
            }

            // If parseItem() failed to consume any tokens we will be stuck in
            // an infinite loop. Detect that here and bail out. If parseItem()
            // did not issue a diagnostic on this token, add one now as well.
            if (current == next) {
                if (!skipBadTokens<IsExpected, IsEnd>(code, true))
                    break;
            }
            current = next;
        }
        closeToken = expect(closeKind);
    }

    template<bool (*IsExpected)(TokenKind), bool (*IsAbort)(TokenKind)>
    bool skipBadTokens(DiagCode code, bool first) {
        auto current = peek();
        do {
            if (current.kind == TokenKind::EndOfFile || IsAbort(current.kind) ||
                syntax::SyntaxFacts::isEndKeyword(current.kind)) {
                return false;
            }

            skipToken(first ? std::make_optional(code) : std::nullopt);
            current = peek();
            first = false;
        } while (!IsExpected(current.kind));

        return true;
    }

private:
    SourceLocation getLastLocation();
    void prependSkippedTokens(Token& node);
    void reportMissingList(Token current, TokenKind closeKind, Token& closeToken, DiagCode code);
    void reportMisplacedSeparator();

    Window window;
    SmallVector<Token> skippedTokens;
    SmallVector<Token> openDelims;
    std::pair<Token, Token> lastPoppedDelims;
};

} // namespace slang::parsing
