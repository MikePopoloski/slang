#pragma once

namespace slang {

class MacroDecl {
public:
    StringRef name;
    ArrayRef<Token*> body;
};

class Preprocessor {
public:
    Preprocessor(SourceTracker& sourceTracker, BumpAllocator& alloc, Diagnostics& diagnostics);

    // look up a keyword by string; returns TokenKind::Unknown if not a keyword
    // note that this uses the preprocessor's current set of keywords, which can
    // be changed dynamically via directives
    TokenKind lookupKeyword(StringRef identifier);

    // called by the active lexer to let the preprocessor parse a directive
    Trivia* parseDirective(Lexer* lexer);

    // lexes a token from the current source on the lexer stack
    // if there are no include files on the stack, this returns null
    Token* lex(Lexer* current);

    SourceTracker& getSourceTracker() const { return sourceTracker; }
    BumpAllocator& getAllocator() const { return alloc; }
    Diagnostics& getDiagnostics() const { return diagnostics; }

private:
    Trivia* handleIncludeDirective(Token* directive);
    Trivia* handleResetAllDirective(Token* directive);
    Trivia* handleDefineDirective(Token* directive);

    Token* parseEndOfDirective();

    Token* peek();
    Token* consume();
    Token* expect(TokenKind kind);

    void addError(DiagCode code);

    SourceTracker& sourceTracker;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;

    std::unordered_map<StringRef, DefineDirectiveTrivia*> macros;
    std::deque<Lexer> lexerStack;
    Lexer* currentLexer;
    Token* currentToken;

    Buffer<Trivia*> triviaBuffer;
    BufferPool<Token*> tokenPool;
    BufferPool<MacroFormalArgument*> argumentPool;

    const StringTable<TokenKind>* keywordTable;

    static constexpr int MaxIncludeDepth = 32;
};

}