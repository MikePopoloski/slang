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
class MacroExpander;

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

    ArrayRef<Token*> parseMacroArg(LexerMode mode);

    bool shouldTakeElseBranch(SourceLocation location, bool isElseIf, StringRef macroName);
    Trivia parseBranchDirective(Token* directive, Token* condition, bool taken);

    void expectTimescaleSpecifier(Token*& unit, Token*& precision);

    Token* peek(LexerMode mode = LexerMode::Directive);
    Token* consume(LexerMode mode = LexerMode::Directive);
    Token* expect(TokenKind kind, LexerMode mode = LexerMode::Directive);
    bool peek(TokenKind kind, LexerMode mode = LexerMode::Directive) { return peek(mode)->kind == kind; }

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

    bool inMacroBody = false;

    const StringTable<TokenKind>* keywordTable;

    static constexpr int MaxSourceDepth = 8192;
};

}