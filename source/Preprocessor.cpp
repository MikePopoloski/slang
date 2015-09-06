#include "slang.h"

namespace slang {

Preprocessor::Preprocessor(Lexer& lexer, FileTracker& fileTracker) :
    mainLexer(lexer), fileTracker(fileTracker) {

    mainLexer.setPreprocessor(this);
}

void Preprocessor::include(StringRef path, bool systemPath) {
    SourceFile* sourceFile = fileTracker.readHeader(getCurrentFile(), path, systemPath);
    if (!sourceFile) {
        // error
    }

    // create a new lexer for this include file and push it onto the stack
    lexerStack.emplace_back(
        sourceFile->id,
        sourceFile->buffer,
        mainLexer.getAllocator(),
        mainLexer.getDiagnostics()
    );
    currentLexer = &lexerStack.back();
    currentLexer->setPreprocessor(this);
}

}