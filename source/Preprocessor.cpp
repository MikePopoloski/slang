#include "slang.h"

namespace slang {

Preprocessor::Preprocessor(FileTracker& fileTracker) :
    fileTracker(fileTracker) {
}

void Preprocessor::enterSourceFile(Lexer* lexer) {
    mainLexer = lexer;
}

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
}

}