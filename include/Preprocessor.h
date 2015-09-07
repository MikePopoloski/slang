#pragma once

namespace slang {

class Preprocessor {
public:
    Preprocessor(FileTracker& fileTracker, BumpAllocator& alloc, Diagnostics& diagnostics);

    void enterFile(StringRef source);
    void enterFile(FileID file, StringRef source);

    Token* lex();

    FileTracker& getFileTracker() const { return fileTracker; }
    BumpAllocator& getAllocator() const { return alloc; }
    Diagnostics& getDiagnostics() const { return diagnostics; }

private:
    FileTracker& fileTracker;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;

    std::deque<Lexer> lexerStack;
    Lexer* currentLexer;
};

}