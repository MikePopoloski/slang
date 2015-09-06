#include "slang.h"

namespace slang {

Preprocessor::Preprocessor(Lexer& lexer, HeaderSearch& headerSearch) :
    mainLexer(lexer), headerSearch(headerSearch) {

    mainLexer.setPreprocessor(this);
}

void Preprocessor::include(StringRef path, bool systemPath) {
    SourceFile* sourceFile = headerSearch.find(getCurrentFile(), path, systemPath);
    if (!sourceFile) {
        // error
    }

    // create a new lexer for this include file and push it onto the stack
    lexerStack.emplace_back(
        sourceFile->file,
        sourceFile->buffer,
        mainLexer.getAllocator(),
        mainLexer.getDiagnostics()
    );
    currentLexer = &lexerStack.back();
    currentLexer->setPreprocessor(this);
}

}