#pragma once

namespace slang {

struct DefineDirectiveSyntax;
struct MacroFormalArgumentSyntax;
struct MacroActualArgumentListSyntax;

SyntaxKind getDirectiveKind(StringRef directive);
StringRef getDirectiveText(SyntaxKind kind);

class MacroExpander {
public:
    MacroExpander(BumpAllocator& alloc, DefineDirectiveSyntax* macro, MacroActualArgumentListSyntax* actualArgs);
    Token* next();

    bool done() const;

private:
    BumpAllocator& alloc;
    Buffer<Token*> tokens;
    Token** current = nullptr;

    void expand(DefineDirectiveSyntax* macro, MacroActualArgumentListSyntax* actualArgs);
};

class Preprocessor {
public:
    Preprocessor(SourceManager& sourceManager, BumpAllocator& alloc, Diagnostics& diagnostics);

    void pushSource(StringRef source);
    void pushSource(const SourceBuffer* buffer);

    Token* next();

    FileID getCurrentFile();

    SourceManager& getSourceManager() const { return sourceManager; }
    BumpAllocator& getAllocator() const { return alloc; }
    Diagnostics& getDiagnostics() const { return diagnostics; }

private:
    Token* next(LexerMode mode);
    Token* nextRaw(LexerMode mode);

    Trivia handleIncludeDirective(Token* directive);
    Trivia handleResetAllDirective(Token* directive);
    Trivia handleDefineDirective(Token* directive);
    Trivia handleMacroUsage(Token* directive);
    Trivia handleIfDefDirective(Token* directive, bool not);
    Trivia handleElseIfDirective(Token* directive);
    Trivia handleElseDirective(Token* directive);
    Trivia handleEndIfDirective(Token* directive);
    Trivia handleTimescaleDirective(Token* directive);

    Token* parseEndOfDirective();

    Trivia createSimpleDirective(Token* directive);

    ArrayRef<Token*> parseMacroArg();

    bool shouldTakeElseBranch(bool isElseIf, StringRef macroName);
    Trivia parseBranchDirective(Token* directive, Token* condition, bool taken);

    void expectTimescaleSpecifier(Token*& unit, Token*& precision);

    Token* peek();
    Token* consume();
    Token* expect(TokenKind kind);
    bool peek(TokenKind kind) { return peek()->kind == kind; }

    void addError(DiagCode code);
    void addError(DiagCode code, SourceLocation location);

    struct Source {
        enum {
            LEXER,
            MACRO
        };
        uint8_t kind;
        union {
            Lexer* lexer;
            MacroExpander* macro;
        };

        Source(Lexer* lexer) : kind(LEXER), lexer(lexer) {}
        Source(MacroExpander* macro) : kind(MACRO), macro(macro) {}
    };

    struct BranchEntry {
        bool anyTaken;
        bool currentActive;
        bool hasElse = false;

        BranchEntry(bool taken) : anyTaken(taken), currentActive(taken) {}
    };

    SourceManager& sourceManager;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;

    std::deque<Source> sourceStack;
    std::deque<BranchEntry> branchStack;
    std::unordered_map<StringRef, DefineDirectiveSyntax*> macros;

    Buffer<TokenKind> delimPairStack;
    BufferPool<Trivia> triviaPool;
    BufferPool<Token*> tokenPool;
    BufferPool<TokenOrSyntax> syntaxPool;

    Token* currentToken;

    const StringTable<TokenKind>* keywordTable;

    static constexpr int MaxSourceDepth = 8192;
};

}