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
        SmallVectorSized<TokenOrSyntax, 32> buffer;
        parseSeparatedList<IsExpected, IsEnd, TParserFunc>(buffer, closeKind, separatorKind, closeToken, code, std::forward<TParserFunc>(parseItem));
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
        if (!IsEnd(current.kind)) {
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
