//------------------------------------------------------------------------------
// ParserBase.h
// Base class for parsing.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/Diagnostics.h"
#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/SmallVector.h"

namespace slang {

class Preprocessor;

/// Base class for the Parser, which contains helpers and language-agnostic parsing routines.
/// Mostly this helps keep the main Parser smaller and more focused.
class ParserBase {
protected:
    ParserBase(Preprocessor& preprocessor);

    Diagnostics& getDiagnostics();
    Diagnostic& addDiag(DiagCode code, SourceLocation location);

    // Helper methods to manipulate the underlying token stream.
    Token peek(uint32_t offset);
    Token peek();
    bool peek(TokenKind kind);
    Token consume();
    Token consumeIf(TokenKind kind);
    Token expect(TokenKind kind);
    void skipToken(std::optional<DiagCode> diagCode);
    void pushTokens(span<const Token> tokens);

    Token missingToken(TokenKind kind, SourceLocation location);

    Token getLastConsumed() const;

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
        uint32_t currentOffset = 0;
        uint32_t count = 0;
        uint32_t capacity = 0;

        void addNew();
        void moveToNext();
        void insertHead(span<const Token> tokens);
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

        TResult result = parseItem();
        Token end = expect(endKind);
        return std::make_tuple(start, end, result);
    }

    enum class AllowEmpty { False, True };

    /// This is a generalized method for parsing a delimiter separated list of things
    /// with bookend tokens in a way that robustly handles bad tokens.
    template<bool (*IsExpected)(TokenKind), bool (*IsEnd)(TokenKind), typename TParserFunc>
    void parseSeparatedList(TokenKind openKind, TokenKind closeKind, TokenKind separatorKind,
                            Token& openToken, span<TokenOrSyntax>& list, Token& closeToken,
                            DiagCode code, TParserFunc&& parseItem, AllowEmpty allowEmpty = {}) {
        openToken = expect(openKind);
        if (openToken.isMissing()) {
            closeToken = missingToken(closeKind, openToken.location());
            list = span<TokenOrSyntax>();
            return;
        }

        SmallVectorSized<TokenOrSyntax, 32> buffer;
        parseSeparatedList<IsExpected, IsEnd, TParserFunc>(
            buffer, closeKind, separatorKind, closeToken, code,
            std::forward<TParserFunc>(parseItem), allowEmpty);
        list = buffer.copy(alloc);
    }

    template<bool (*IsExpected)(TokenKind), bool (*IsEnd)(TokenKind), typename TParserFunc>
    void parseSeparatedList(SmallVector<TokenOrSyntax>& buffer, TokenKind closeKind,
                            TokenKind separatorKind, Token& closeToken, DiagCode code,
                            TParserFunc&& parseItem, AllowEmpty allowEmpty = {}) {
        auto current = peek();
        if (IsEnd(current.kind)) {
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
            current = peek();
            buffer.append(parseItem());

            // If we found the end token, we're done with list processing.
            if (IsEnd(peek().kind))
                break;

            // If the next token isn't expected, try skipping over some tokens until
            // we find a good place to continue.
            if (!IsExpected(peek().kind)) {
                if (!skipBadTokens<IsExpected, IsEnd>(code))
                    break;

                // We're back on track; continue on below to make sure we get a
                // separator into the output buffer.
            }

            buffer.append(expect(separatorKind));

            if (IsEnd(peek().kind)) {
                if (allowEmpty == AllowEmpty::True)
                    continue;

                // Specific check for misplaced trailing separators here.
                reportMisplacedSeparator();
                break;
            }

            // If parseItem() failed to consume any tokens we will be stuck in
            // an infinite loop. Detect that here and bail out. If parseItem()
            // did not issue a diagnostic on this token, add one now as well.
            if (current.getInfo() == peek().getInfo()) {
                Diagnostics& diags = getDiagnostics();
                auto location = getLastLocation();
                bool needDiag = diags.empty() || (diags.back().location != location &&
                                                  diags.back().location != current.location());

                skipToken(needDiag ? std::make_optional(code) : std::nullopt);
                if (IsEnd(peek().kind) || !skipBadTokens<IsExpected, IsEnd>(code))
                    break;
            }
        }
        closeToken = expect(closeKind);
    }

    template<bool (*IsExpected)(TokenKind), bool (*IsAbort)(TokenKind)>
    bool skipBadTokens(DiagCode code) {
        auto current = peek();
        bool first = true;

        while (!IsExpected(current.kind)) {
            if (current.kind == TokenKind::EndOfFile || IsAbort(current.kind))
                return false;

            skipToken(first ? std::make_optional(code) : std::nullopt);
            current = peek();
            first = false;
        }
        return true;
    }

private:
    SourceLocation getLastLocation();
    void prependSkippedTokens(Token& node);
    void reportMissingList(Token current, TokenKind closeKind, Token& closeToken, DiagCode code);
    void reportMisplacedSeparator();

    Window window;
    SmallVectorSized<Token, 4> skippedTokens;
};

} // namespace slang
