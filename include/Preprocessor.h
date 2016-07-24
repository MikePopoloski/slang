#pragma once

#include <cstdint>
#include <deque>
#include <unordered_map>

#include "Buffer.h"
#include "BufferPool.h"
#include "Diagnostics.h"
#include "Lexer.h"
#include "SourceLocation.h"
#include "StringRef.h"
#include "SyntaxNode.h"
#include "Token.h"

namespace slang {

struct DefineDirectiveSyntax;
struct MacroActualArgumentListSyntax;
struct MacroFormalArgumentListSyntax;
struct MacroActualArgumentSyntax;
struct MacroFormalArgumentSyntax;

StringRef getDirectiveText(SyntaxKind kind);

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
    Trivia handleElsIfDirective(Token* directive);
    Trivia handleElseDirective(Token* directive);
    Trivia handleEndIfDirective(Token* directive);
    Trivia handleTimescaleDirective(Token* directive);
    Trivia handleDefaultNetTypeDirective(Token* directive);

    Token* parseEndOfDirective(bool suppressError = false);
    Trivia createSimpleDirective(Token* directive, bool suppressError = false);

    bool shouldTakeElseBranch(SourceLocation location, bool isElseIf, StringRef macroName);
    Trivia parseBranchDirective(Token* directive, Token* condition, bool taken);

    void expectTimescaleSpecifier(Token*& unit, Token*& precision);

    DefineDirectiveSyntax* findMacro(Token* directive);
    void expandMacro(DefineDirectiveSyntax* definition, MacroActualArgumentListSyntax* actualArgs, Buffer<Token*>& dest);
    void expandReplacementList(ArrayRef<Token*> tokens, Buffer<Token*>& dest);

    // functions to advance the underlying token stream
    Token* peek(LexerMode mode = LexerMode::Directive);
    Token* consume(LexerMode mode = LexerMode::Directive);
    Token* expect(TokenKind kind, LexerMode mode = LexerMode::Directive);
    bool peek(TokenKind kind, LexerMode mode = LexerMode::Directive) { return peek(mode)->kind == kind; }

    void addError(DiagCode code);
    void addError(DiagCode code, SourceLocation location);

    struct BranchEntry {
        bool anyTaken;
        bool currentActive;
        bool hasElse = false;

        BranchEntry(bool taken) : anyTaken(taken), currentActive(taken) {}
    };

    // helper class for parsing macro arguments
    class MacroParser {
    public:
        MacroParser(Preprocessor& preprocessor) : pp(preprocessor) {}

        void setBuffer(ArrayRef<Token*> newBuffer) {
            this->buffer = newBuffer;

        }

        Token* next() {
            return nullptr;
        }

        MacroActualArgumentListSyntax* parseActualArgumentList();
        MacroFormalArgumentListSyntax* parseFormalArgumentList();

    private:
        template<typename TFunc>
        void parseArgumentList(Buffer<TokenOrSyntax>& buffer, TFunc&& parseItem);

        MacroActualArgumentSyntax* parseActualArgument();
        MacroFormalArgumentSyntax* parseFormalArgument();
        ArrayRef<Token*> parseTokenList();

        Token* peek() { return pp.peek(currentMode); }
        Token* consume() { return pp.consume(currentMode); }
        Token* expect(TokenKind kind) { return pp.expect(kind, currentMode); }
        bool peek(TokenKind kind) { return peek()->kind == kind; }

        Preprocessor& pp;
        ArrayRef<Token*> buffer;
        Token* currentToken;
        LexerMode currentMode;
    };

    SourceManager& sourceManager;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;

    // stack of active lexers; each `include pushes a new lexer
    std::deque<Lexer*> lexerStack;

    // keep track of nested processor branches (ifdef, ifndef, else, elsif, endif)
    std::deque<BranchEntry> branchStack;

    // map from macro name to macro definition
    std::unordered_map<StringRef, DefineDirectiveSyntax*> macros;

    // when parsing macros, keep track of paired delimiters
    Buffer<TokenKind> delimPairStack;

    // scratch space for mapping macro formal parameters to argument values
    std::unordered_map<StringRef, const TokenList*> argumentMap;

    // list of expanded macro tokens to drain before continuing with active lexer
    Buffer<Token*> expandedTokens;
    Token** currentMacroToken = nullptr;

    // pools for constructing lists of trivia, tokens, syntax nodes
    BufferPool<Trivia> triviaPool;
    BufferPool<Token*> tokenPool;
    BufferPool<TokenOrSyntax> syntaxPool;

    // the latest token pulled from a lexer
    Token* currentToken;

    // we adjust lexing behavior slightly when lexing within a macro body
    bool inMacroBody = false;

    // the currently active set of keywords; this can be changed by compilation directives
    const StringTable<TokenKind>* keywordTable;

    // maximum number of nested includes
    static constexpr int MaxIncludeDepth = 1024;
};

}