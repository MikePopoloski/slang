#include "slang.h"

namespace slang {

Preprocessor::Preprocessor(FileTracker& fileTracker, BumpAllocator& alloc, Diagnostics& diagnostics) :
    fileTracker(fileTracker), alloc(alloc), diagnostics(diagnostics), currentLexer(nullptr) {
}

void Preprocessor::enterFile(StringRef source) {
    // TODO: expand this a bit
    enterFile(fileTracker.track("unnamed"), source);
}

void Preprocessor::enterFile(FileID file, StringRef source) {
    // TODO: max include depth
    // create a new lexer for this file and push it onto the stack
    lexerStack.emplace_back(file, source, alloc, diagnostics);
    currentLexer = &lexerStack.back();
}

Token* Preprocessor::lex() {
    // TODO: preprocessing
    ASSERT(currentLexer);
    return currentLexer->lex();
}

/*
void Preprocessor::include(StringRef path, bool systemPath) {
    ASSERT(mainLexer);

    SourceFile* sourceFile = fileTracker.readHeader(getCurrentFile(), path, systemPath);
    if (!sourceFile) {
        return;
    }

    // create a new lexer for this include file and push it onto the stack
    lexerStack.emplace_back(
        sourceFile->id,
        sourceFile->buffer,
        *this,
        mainLexer->getAllocator(),
        mainLexer->getDiagnostics()
    );
    currentLexer = &lexerStack.back();
}

Token* Preprocessor::next() {
    ASSERT(currentLexer);
    Token* token = currentLexer->lex();
    ASSERT(token);

    if (token->kind == TokenKind::EndOfFile) {
        lexerStack.pop_back();
        if (lexerStack.empty())
            currentLexer = nullptr;
        else
            currentLexer = &lexerStack.back();
    }

    return token;
}*/

}