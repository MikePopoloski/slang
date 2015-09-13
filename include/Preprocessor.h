#pragma once

namespace slang {

class Preprocessor {
public:
    Preprocessor(SourceTracker& sourceTracker, BumpAllocator& alloc, Diagnostics& diagnostics);

    void enterFile(SourceText source);
    void enterFile(FileID file, SourceText source);

    Token* lex();

    TokenKind lookupKeyword(StringRef identifier);

    Trivia* parseDirective(Lexer* lexer);

    SourceTracker& getSourceTracker() const { return sourceTracker; }
    BumpAllocator& getAllocator() const { return alloc; }
    Diagnostics& getDiagnostics() const { return diagnostics; }

private:
    Token* handleInclude(Token* directiveToken);
    Token* handleIdentifier(Token* token);

    Trivia* parseIncludeDirective(Token* directive);
    Token* parseEndOfDirective();

    Token* peek();
    Token* consume();
    Token* expect(TokenKind kind);

    void addError(DiagCode code);

    SourceTracker& sourceTracker;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;

    std::deque<Lexer> lexerStack;
    Lexer* currentLexer;
    Token* currentToken;

    Buffer<Trivia> triviaBuffer;

    const StringTable<TokenKind>* keywordTable;
};

}