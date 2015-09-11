#pragma once

namespace slang {

class Preprocessor : TokenConsumer<Lexer, 32> {
public:
    Preprocessor(SourceTracker& sourceTracker, BumpAllocator& alloc, Diagnostics& diagnostics);

    void enterFile(SourceText source);
    void enterFile(FileID file, SourceText source);

    Token* lex();

    TokenKind lookupKeyword(StringRef identifier);

    SourceTracker& getSourceTracker() const { return sourceTracker; }
    BumpAllocator& getAllocator() const { return alloc; }
    Diagnostics& getDiagnostics() const { return diagnostics; }

private:
    Token* handleInclude(Token* directiveToken);
    Token* handleIdentifier(Token* token);

    void addError(DiagCode code);
    void convertDirectiveToTrivia(Token* directive);

    SourceTracker& sourceTracker;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;

    std::deque<Lexer> lexerStack;
    Buffer<Trivia> triviaBuffer;

    const StringTable<TokenKind>* keywordTable;
};

}