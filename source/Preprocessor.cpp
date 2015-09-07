#include "slang.h"

namespace slang {

Preprocessor::Preprocessor(FileTracker& fileTracker, BumpAllocator& alloc, Diagnostics& diagnostics) :
    fileTracker(fileTracker), alloc(alloc), diagnostics(diagnostics) {
}

void Preprocessor::enterFile(StringRef source) {
    // TODO: expand this a bit
    enterFile(fileTracker.track("unnamed"), source);
}

void Preprocessor::enterFile(FileID file, StringRef source) {
    // TODO: max include depth
    // create a new lexer for this file and push it onto the stack
    lexerStack.emplace_back(file, source, alloc, diagnostics);
    setSource(&lexerStack.back());
}

Token* Preprocessor::lex() {
    while (true) {
        Token* token = consume();
        switch (token->kind) {
            case TokenKind::Identifier:
                return handleIdentifier();
            case TokenKind::EndOfFile:
                lexerStack.pop_back();
                if (lexerStack.empty())
                    setSource(nullptr);
                else
                    setSource(&lexerStack.back());
                return token;
            case TokenKind::Directive:
                switch (token->directiveKind()) {
                    case TriviaKind::IncludeDirective: return handleInclude();
                }
                break;
            default:
                // pass through to the caller
                return token;
        }
    }
}

Token* Preprocessor::handleInclude() {
    return nullptr;
}

}