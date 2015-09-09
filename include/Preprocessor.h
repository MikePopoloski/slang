#pragma once

namespace slang {

class Preprocessor : TokenConsumer<Lexer, 32> {
public:
    Preprocessor(FileTracker& fileTracker, BumpAllocator& alloc, Diagnostics& diagnostics);

    void enterFile(SourceBuffer source);
    void enterFile(FileID file, SourceBuffer source);

    Token* lex();

    FileTracker& getFileTracker() const { return fileTracker; }
    BumpAllocator& getAllocator() const { return alloc; }
    Diagnostics& getDiagnostics() const { return diagnostics; }

private:
    Token* handleInclude(Token* directiveToken);
    Token* handleIdentifier(Token* token);

    void addError(DiagCode code);
    void convertDirectiveToTrivia(Token* directive);

    FileTracker& fileTracker;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;

    std::deque<Lexer> lexerStack;
    Buffer<Trivia> triviaBuffer;

    const StringTable<TokenKind>* keywordTable;
};

}