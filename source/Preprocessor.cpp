#include <cstdint>
#include <memory>
#include <string>
#include <filesystem>
#include <unordered_map>
#include <deque>
#include <set>

#include "BumpAllocator.h"
#include "Buffer.h"
#include "StringRef.h"
#include "Diagnostics.h"
#include "FileTracker.h"
#include "Token.h"
#include "Lexer.h"
#include "TokenConsumer.h"
#include "StringTable.h"
#include "SyntaxFacts.h"
#include "Preprocessor.h"

namespace slang {

Preprocessor::Preprocessor(FileTracker& fileTracker, BumpAllocator& alloc, Diagnostics& diagnostics) :
    fileTracker(fileTracker), alloc(alloc), diagnostics(diagnostics) {

    keywordTable = getKeywordTable();
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
                return handleIdentifier(token);
            case TokenKind::EndOfFile:
                lexerStack.pop_back();
                if (lexerStack.empty())
                    setSource(nullptr);
                else
                    setSource(&lexerStack.back());
                return token;
            case TokenKind::Directive:
                switch (token->directiveKind()) {
                    case TriviaKind::IncludeDirective:
                        handleInclude(token);
                        break;
                }
                break;
            default:
                // pass through to the caller
                return token;
        }
    }
}

Token* Preprocessor::handleIdentifier(Token* token) {
    // this identifier might actually be a keyword token
    if (token->identifierType() != IdentifierType::Escaped) {
        TokenKind keywordKind;
        if (keywordTable->lookup(token->valueText(), keywordKind))
            return alloc.emplace<Token>(keywordKind, nullptr, token->trivia);
    }

    return token;
}

void Preprocessor::handleInclude(Token* directiveToken) {
    // next token needs to be the filename
    Token* fileName = consume();
    bool systemPath;
    switch (fileName->kind) {
        case TokenKind::UserIncludeFileName: systemPath = false; break;
        case TokenKind::SystemIncludeFileName: systemPath = true; break;
        default:
            return;
    }

    SourceFile* file = fileTracker.readHeader(getSource()->getFile(), fileName->valueText(), systemPath);
    if (!file)
        return;

    // TODO: attach trivia

    enterFile(file->id, StringRef(file->buffer));
}

}