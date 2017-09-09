//------------------------------------------------------------------------------
// ParserBase.h
// Base class for parsing.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "diagnostics/Diagnostics.h"
#include "lexing/Token.h"
#include "text/SourceLocation.h"
#include "util/SmallVector.h"

#include "SyntaxNode.h"

namespace slang {

class Preprocessor;

/// Base class for the Parser, which contains helpers and language-agnostic parsing routines.
/// Mostly this helps keep the main Parser smaller and more focused.
class ParserBase {
protected:
    ParserBase(Preprocessor& preprocessor);

    Diagnostics& getDiagnostics();
    Diagnostic& addError(DiagCode code, SourceLocation location);

    // Helper methods to manipulate the underlying token stream.
    Token peek(int offset);
    Token peek();
    bool peek(TokenKind kind);
    Token consume();
    Token consumeIf(TokenKind kind);
    Token expect(TokenKind kind);
    SourceLocation skipToken();

    /// Helper class that maintains a sliding window of tokens, with lookahead.
    class Window {
    public:
        explicit Window(Preprocessor& source) :
            tokenSource(source)
        {
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
        int currentOffset = 0;
        int count = 0;
        int capacity = 0;

        void addNew();
        void moveToNext();
    };

    BumpAllocator& alloc;

    enum class SkipAction {
        Continue,
        Abort
    };

    template<typename T, typename... Args>
    T& allocate(Args&&... args) {
        return *alloc.emplace<T>(std::forward<Args>(args)...);
    }

    /// Generalized helper method for parsing a group of things that are bookended by
    /// known token kinds. The point of wrapping it in a function is that if the starting
    /// token is missing, we don't even bother trying to parse the rest of the group.
    template<typename TParserFunc,
             typename TResult = decltype(std::declval<typename std::decay<TParserFunc>::type&>()())>
    std::tuple<Token, Token, TResult>
    parseGroupOrSkip(TokenKind startKind, TokenKind endKind, TParserFunc&& parseItem) {
        Token start = expect(startKind);
        if (start.isMissing())
            return std::make_tuple(start, Token::createMissing(alloc, endKind, start.location()), nullptr);

        TResult result = parseItem();
        Token end = expect(endKind);
        return std::make_tuple(start, end, result);
    }

    /// This is a generalized method for parsing a delimiter separated list of things
    /// with bookend tokens in a way that robustly handles bad tokens.
    template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
    void parseSeparatedList(
        TokenKind openKind,
        TokenKind closeKind,
        TokenKind separatorKind,
        Token& openToken,
        span<TokenOrSyntax>& list,
        Token& closeToken,
        DiagCode code,
        TParserFunc&& parseItem
    ) {
        openToken = expect(openKind);
        if (openToken.isMissing()) {
            closeToken = Token::createMissing(alloc, closeKind, openToken.location());
            list = nullptr;
            return;
        }

        SmallVectorSized<TokenOrSyntax, 32> buffer;
        parseSeparatedList<IsExpected, IsEnd, TParserFunc>(buffer, closeKind, separatorKind, closeToken,
                                                           code, std::forward<TParserFunc>(parseItem));
        list = buffer.copy(alloc);
    }

    template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
    void parseSeparatedList(
        SmallVector<TokenOrSyntax>& buffer,
        TokenKind closeKind,
        TokenKind separatorKind,
        Token& closeToken,
        DiagCode code,
        TParserFunc&& parseItem
    ) {
        auto current = peek();
        if (IsEnd(current.kind)) {
            closeToken = expect(closeKind);
            return;
        }

        // If the very first token isn't expected and there is already an
        // error issued at this location, just bail out of list parsing.
        if (!IsExpected(current.kind)) {
            Diagnostics& diagnostics = getDiagnostics();
            if (!diagnostics.empty() && diagnostics.back().code == DiagCode::ExpectedToken &&
                diagnostics.back().location == current.location()) {

                closeToken = Token::createMissing(alloc, closeKind, current.location());
                return;
            }
        }

        while (true) {
            if (IsExpected(current.kind)) {
                buffer.append(&parseItem(true));
                while (true) {
                    current = peek();
                    if (IsEnd(current.kind))
                        break;

                    if (IsExpected(current.kind)) {
                        buffer.append(expect(separatorKind));
                        buffer.append(&parseItem(false));
                        continue;
                    }

                    if (skipBadTokens<IsExpected, IsEnd>(code) == SkipAction::Abort)
                        break;
                }
                // found the end
                break;
            }
            else if (skipBadTokens<IsExpected, IsEnd>(code) == SkipAction::Abort)
                break;
            else
                current = peek();
        }
        closeToken = expect(closeKind);
    }

    template<bool(*IsExpected)(TokenKind), bool(*IsAbort)(TokenKind)>
    SkipAction skipBadTokens(DiagCode code) {
        auto result = SkipAction::Continue;
        auto current = peek();
        bool error = false;

        while (!IsExpected(current.kind)) {
            if (!error) {
                addError(code, current.location());
                error = true;
            }

            if (current.kind == TokenKind::EndOfFile || IsAbort(current.kind)) {
                result = SkipAction::Abort;
                break;
            }
            skipToken();
            current = peek();
        }
        return result;
    }

private:
    void prependSkippedTokens(Token& node);

    Window window;
    Vector<Token> skippedTokens;
};

}
