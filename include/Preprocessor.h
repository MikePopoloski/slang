#pragma once

namespace slang {

class Preprocessor : TokenConsumer<Lexer, 32> {
public:
    Preprocessor(FileTracker& fileTracker, BumpAllocator& alloc, Diagnostics& diagnostics);

    void enterFile(StringRef source);
    void enterFile(FileID file, StringRef source);

    Token* lex();

    FileTracker& getFileTracker() const { return fileTracker; }
    BumpAllocator& getAllocator() const { return alloc; }
    Diagnostics& getDiagnostics() const { return diagnostics; }

private:
    Token* handleInclude();
    Token* handleIdentifier(Token* token);

    FileTracker& fileTracker;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;

    std::deque<Lexer> lexerStack;
    const StringTable<TokenKind>* keywordTable;
};

}