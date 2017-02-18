//------------------------------------------------------------------------------
// Preprocessor.h
// SystemVerilog preprocessor and directive support.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>
#include <deque>
#include <unordered_map>

#include "diagnostics/Diagnostics.h"
#include "parsing/SyntaxNode.h"
#include "text/SourceLocation.h"
#include "util/SmallVector.h"
#include "util/StringRef.h"
#include "Lexer.h"
#include "Token.h"

namespace slang {

struct DefineDirectiveSyntax;
struct MacroActualArgumentListSyntax;
struct MacroFormalArgumentListSyntax;
struct MacroActualArgumentSyntax;
struct MacroFormalArgumentSyntax;

StringRef getDirectiveText(SyntaxKind kind);

/// Preprocessor - Interface between lexer and parser
///
/// This class handles the messy interface between various source file lexers, include directives,
/// and macro expansion, and the actual SystemVerilog parser that wants a nice coherent stream
/// of tokens to consume.
class Preprocessor {
public:
    Preprocessor(SourceManager& sourceManager, BumpAllocator& alloc, Diagnostics& diagnostics);

    /// Push a new source file onto the stack.
    void pushSource(StringRef source);
    void pushSource(SourceBuffer buffer);

    /// Gets the next token in the stream, after applying preprocessor rules.
    Token next();

    SourceManager& getSourceManager() const { return sourceManager; }
    BumpAllocator& getAllocator() const { return alloc; }
    Diagnostics& getDiagnostics() const { return diagnostics; }

private:
    // Internal methods to grab and handle the next token
    Token next(LexerMode mode);
    Token nextRaw(LexerMode mode);

    // directive handling methods
    Trivia handleIncludeDirective(Token directive);
    Trivia handleResetAllDirective(Token directive);
    Trivia handleDefineDirective(Token directive);
    Trivia handleMacroUsage(Token directive);
    Trivia handleIfDefDirective(Token directive, bool inverted);
    Trivia handleElsIfDirective(Token directive);
    Trivia handleElseDirective(Token directive);
    Trivia handleEndIfDirective(Token directive);
    Trivia handleTimescaleDirective(Token directive);
    Trivia handleDefaultNetTypeDirective(Token directive);
    Trivia handleLineDirective(Token directive);
    Trivia handleUndefDirective(Token directive);
    Trivia handleUndefineAllDirective(Token directive);
    Trivia handleBeginKeywordsDirective(Token directive);
    Trivia handleEndKeywordsDirective(Token directive);

    // Shared method to consume up to the end of a directive line
    Token parseEndOfDirective(bool suppressError = false);
    Trivia createSimpleDirective(Token directive, bool suppressError = false);

    // Determines whether the else branch of a conditional directive should be taken
    bool shouldTakeElseBranch(SourceLocation location, bool isElseIf, StringRef macroName);

    // Handle parsing a branch of a conditional directive
    Trivia parseBranchDirective(Token directive, Token condition, bool taken);

    // Timescale specifier parser
    bool expectTimescaleSpecifier(Token& unit, Token& precision);

    // Macro handling methods
    DefineDirectiveSyntax* findMacro(Token directive);
    MacroActualArgumentListSyntax* handleTopLevelMacro(Token directive);
    bool expandMacro(DefineDirectiveSyntax* definition, Token usageSite, MacroActualArgumentListSyntax* actualArgs, SmallVector<Token>& dest);
    bool expandReplacementList(ArrayRef<Token>& tokens);

    // functions to advance the underlying token stream
    Token peek(LexerMode mode = LexerMode::Directive);
    Token consume(LexerMode mode = LexerMode::Directive);
    Token expect(TokenKind kind, LexerMode mode = LexerMode::Directive);
    bool peek(TokenKind kind, LexerMode mode = LexerMode::Directive) { return peek(mode).kind == kind; }

    Diagnostic& addError(DiagCode code, SourceLocation location);

    // This is a small collection of state used to keep track of where we are in a tree of
    // nested conditional directives.
    struct BranchEntry {
        // Whether any of the sibling directives in this branch have been taken; used to decide whether
        // to take an `elsif or `else branch.
        bool anyTaken;

        // Whether the current branch is active.
        bool currentActive;

        // Has this chain of conditional directives had an `else directive yet; it's an error
        // for any other directives in the current level to come after that.
        bool hasElse = false;

        BranchEntry(bool taken) : anyTaken(taken), currentActive(taken) {}
    };

    // Helper class for parsing macro arguments. There's a lot of otherwise overlapping code that this
    // class consolidates, but it makes it a little confusing. If a buffer is provided via setBuffer(),
    // tokens are pulled from there first. Otherwise it just pulls from the main preprocessor stream.
    class MacroParser {
    public:
        MacroParser(Preprocessor& preprocessor) : pp(preprocessor) {}

        // Set a buffer to use first, in order, before looking at an underlying preprocessor
        // stream for macro argument lists.
        void setBuffer(ArrayRef<Token> newBuffer);

        // Pull tokens one at a time from a previously set buffer. Note that this won't pull
        // from the underlying preprocessor stream; its purpose is to allow stepping through
        // a macro replacement list.
        Token next();

        MacroActualArgumentListSyntax* parseActualArgumentList();
        MacroFormalArgumentListSyntax* parseFormalArgumentList();

    private:
        template<typename TFunc>
        void parseArgumentList(SmallVector<TokenOrSyntax>& buffer, TFunc&& parseItem);

        MacroActualArgumentSyntax* parseActualArgument();
        MacroFormalArgumentSyntax* parseFormalArgument();
        ArrayRef<Token> parseTokenList();

        Token peek();
        Token consume();
        Token expect(TokenKind kind);
        bool peek(TokenKind kind) { return peek().kind == kind; }

        Preprocessor& pp;
        ArrayRef<Token> buffer;
        uint32_t currentIndex = 0;

        // When we're parsing formal arguments, we're in directive mode since the macro needs to
        // end at the current line (unless there's a continuation character). For actual arguments,
        // we want to freely span multiple lines.
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

    // scratch space for mapping macro formal parameters to argument values
    std::unordered_map<StringRef, const TokenList*> argumentMap;

    // list of expanded macro tokens to drain before continuing with active lexer
    SmallVectorSized<Token, 16> expandedTokens;
    Token* currentMacroToken = nullptr;

    // the latest token pulled from a lexer
    Token currentToken;

    // the last token consumed before the currentToken; used to back up and
    // report errors in a different location in certain scenarios
    Token lastConsumed;

    // we adjust lexing behavior slightly when lexing within a macro body
    bool inMacroBody = false;

    // The stack of changes to which keyword versions to use, pushed to by
    // `begin_keywords, popped to by `end_keywords
    std::vector<KeywordVersion> keywordVersionStack;

    // maximum number of nested includes
    static constexpr int MaxIncludeDepth = 1024;
};

}
