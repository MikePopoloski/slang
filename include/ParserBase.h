//------------------------------------------------------------------------------
// ParserBase.h
// Base class for parsing.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "Buffer.h"
#include "BufferPool.h"
#include "Diagnostics.h"
#include "SourceLocation.h"
#include "SyntaxNode.h"
#include "Token.h"

namespace slang {

class Preprocessor;

/// Base class for the Parser, which contains helpers and language-agnostic parsing routines.
/// Mostly this helps keep the main Parser smaller and more focused.
class ParserBase {
protected:
    ParserBase(Preprocessor& preprocessor);

	/// Preprend trivia to the given syntax node / token.
    SyntaxNode* prependTrivia(SyntaxNode* node, Trivia* trivia);
    Token prependTrivia(Token token, Trivia* trivia);

	/// Prepend a set of trivia to the given syntax node / token.
    void prependTrivia(SyntaxNode* node, Buffer<Trivia>& trivia);
    Token prependTrivia(Token token, Buffer<Trivia>& trivia);

	/// Prepend a set of skipped tokens to the given syntax node / token.
    SyntaxNode* prependSkippedTokens(SyntaxNode* node, Buffer<Token>& tokens);
    Token prependSkippedTokens(Token node, Buffer<Token>& tokens);

	/// Reduce the given skipped tokens into trivia in the given buffer.
    void reduceSkippedTokens(Buffer<Token>& skipped, Buffer<Trivia>& trivia);

    Diagnostics& getDiagnostics();
    Diagnostic& addError(DiagCode code, SourceLocation location);

	// Helper methods to manipulate the underlying token stream.
    Token peek(int offset);
    Token peek();
    bool peek(TokenKind kind);
    Token consume();
    Token consumeIf(TokenKind kind);
    Token expect(TokenKind kind);

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
    BufferPool<Trivia> triviaPool;
    BufferPool<Token> tokenPool;
    BufferPool<SyntaxNode*> nodePool;
    BufferPool<TokenOrSyntax> tosPool;

    enum class SkipAction {
        Continue,
        Abort
    };

    /// This is a generalized method for parsing a delimiter separated list of things
    /// with bookend tokens in a way that robustly handles bad tokens.
    template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
    void parseSeparatedList(
        TokenKind openKind,
        TokenKind closeKind,
        TokenKind separatorKind,
        Token& openToken,
        ArrayRef<TokenOrSyntax>& list,
        Token& closeToken,
        DiagCode code,
        TParserFunc&& parseItem
    ) {
        openToken = expect(openKind);

        auto buffer = tosPool.get();
        parseSeparatedList<IsExpected, IsEnd, TParserFunc>(buffer, closeKind, separatorKind, closeToken, code, std::forward<TParserFunc>(parseItem));
        list = buffer->copy(alloc);
    }

    template<bool(*IsExpected)(TokenKind), bool(*IsEnd)(TokenKind), typename TParserFunc>
    void parseSeparatedList(
        Buffer<TokenOrSyntax>& buffer,
        TokenKind closeKind,
        TokenKind separatorKind,
        Token& closeToken,
        DiagCode code,
        TParserFunc&& parseItem
    ) {
        Trivia skippedTokens;
        auto current = peek();
        if (!IsEnd(current.kind)) {
            while (true) {
                if (IsExpected(current.kind)) {
                    buffer.append(prependTrivia(parseItem(true), &skippedTokens));
                    while (true) {
                        current = peek();
                        if (IsEnd(current.kind))
                            break;

                        if (IsExpected(current.kind)) {
                            buffer.append(prependTrivia(expect(separatorKind), &skippedTokens));
                            buffer.append(prependTrivia(parseItem(false), &skippedTokens));
                            continue;
                        }

                        if (skipBadTokens<IsExpected, IsEnd>(&skippedTokens, code) == SkipAction::Abort)
                            break;
                    }
                    // found the end
                    break;
                }
                else if (skipBadTokens<IsExpected, IsEnd>(&skippedTokens, code) == SkipAction::Abort)
                    break;
                else
                    current = peek();
            }
        }
        closeToken = prependTrivia(expect(closeKind), &skippedTokens);
    }

    template<bool(*IsExpected)(TokenKind), bool(*IsAbort)(TokenKind)>
    SkipAction skipBadTokens(Trivia* skippedTokens, DiagCode code) {
        auto tokens = tokenPool.get();
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
            tokens->append(consume());
            current = peek();
        }

        if (tokens->empty())
            *skippedTokens = Trivia();
        else
            *skippedTokens = Trivia(TriviaKind::SkippedTokens, tokens->copy(alloc));

        return result;
    }

    template<typename T>
    void prependTrivia(ArrayRef<T*> list, Trivia* trivia) {
        if (trivia->kind != TriviaKind::Unknown && !list.empty())
            prependTrivia(*list.begin(), trivia);
    }

private:
    Window window;
};

}