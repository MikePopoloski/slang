//------------------------------------------------------------------------------
// Preprocessor.h
// SystemVerilog preprocessor and directive support.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <deque>
#include <unordered_map>

#include "slang/diagnostics/Diagnostics.h"
#include "slang/parsing/Lexer.h"
#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Bag.h"
#include "slang/util/SmallVector.h"
#include "slang/util/StackContainer.h"

namespace slang {

struct DefineDirectiveSyntax;
struct MacroActualArgumentListSyntax;
struct MacroFormalArgumentListSyntax;
struct MacroActualArgumentSyntax;
struct MacroFormalArgumentSyntax;

string_view getDirectiveText(SyntaxKind kind);

/// Contains various options that can control preprocessing behavior.
struct PreprocessorOptions {
    /// The maximum depth of the include stack; further attempts to include
    /// a file will result in an error.
    uint32_t maxIncludeDepth = 1024;

    /// The name to associate with errors produced by macros specified
    /// via the @a predefines option.
    std::string predefineSource = "<api>";

    /// A set of macros to predefine, of the form <macro>=<value> or
    /// just <macro> to predefine to a value of 1.
    std::vector<std::string> predefines;

    /// A set of macro names to undefine at the start of file preprocessing.
    std::vector<std::string> undefines;
};

/// Preprocessor - Interface between lexer and parser
///
/// This class handles the messy interface between various source file lexers, include directives,
/// and macro expansion, and the actual SystemVerilog parser that wants a nice coherent stream
/// of tokens to consume.
class Preprocessor {
public:
    Preprocessor(SourceManager& sourceManager, BumpAllocator& alloc, Diagnostics& diagnostics,
                 const Bag& options = {});

    /// Gets the next token in the stream, after applying preprocessor rules.
    Token next();

    /// Push a new source file onto the stack.
    void pushSource(string_view source, string_view name = "");
    void pushSource(SourceBuffer buffer);

    /// Predefines the given macro definition. The given definition string is lexed
    /// as if it were source text immediately following a `define directive.
    /// If any diagnostics are printed for the created text, they will be marked
    /// as coming from @a fileName.
    void predefine(string_view definition, string_view fileName = "<api>");

    /// Undefines a previously defined macro. If the macro is not defined, or
    /// if you pass the name of an intrinsic macro, this call returns false and
    /// does not undefine anything.
    bool undefine(string_view name);

    /// Undefines all currently defined macros.
    void undefineAll();

    /// Checks whether the given macro is defined. This does not check built-in
    /// directives except for the intrinsic macros (__LINE__, etc).
    bool isDefined(string_view name);

    /// Sets the base keyword version for the current compilation unit. Note that this does not
    /// affect the keyword version if the user has explicitly requested a different
    /// version via the begin_keywords directive.
    void setKeywordVersion(KeywordVersion version);

    /// Resets the state of all compiler directives; this is equivalent to encountering the
    /// `resetall directive in source. Note that this does not include the state of any
    /// macros that have been defined.
    void resetAllDirectives();

    /// Gets the currently active time scale value, if any has been set by the user.
    const optional<TimeScale>& getTimeScale() const { return activeTimeScale; }

    /// Gets the default net type to use if none is specified. This is set via
    /// the `default_nettype directive. If it is set to "none" by the user, this
    /// will return TokenKind::Unknown.
    TokenKind getDefaultNetType() const { return defaultNetType; }

    /// Gets the currently active keyword version in use by the preprocessor.
    KeywordVersion getCurrentKeywordVersion() const { return keywordVersionStack.back(); }

    SourceManager& getSourceManager() const { return sourceManager; }
    BumpAllocator& getAllocator() const { return alloc; }
    Diagnostics& getDiagnostics() const { return diagnostics; }

private:
    // Internal methods to grab and handle the next token
    Token nextProcessed();
    Token nextRaw();

    // directive handling methods
    Token handleDirectives(Token token);
    Trivia handleIncludeDirective(Token directive);
    Trivia handleResetAllDirective(Token directive);
    Trivia handleDefineDirective(Token directive);
    Trivia handleMacroUsage(Token directive);
    Trivia handleIfDefDirective(Token directive, bool inverted);
    Trivia handleElsIfDirective(Token directive);
    Trivia handleElseDirective(Token directive);
    Trivia handleEndIfDirective(Token directive);
    Trivia handleTimeScaleDirective(Token directive);
    Trivia handleDefaultNetTypeDirective(Token directive);
    Trivia handleLineDirective(Token directive);
    Trivia handleUndefDirective(Token directive);
    Trivia handleUndefineAllDirective(Token directive);
    Trivia handleBeginKeywordsDirective(Token directive);
    Trivia handleEndKeywordsDirective(Token directive);
    Trivia createSimpleDirective(Token directive);

    // Determines whether the else branch of a conditional directive should be taken
    bool shouldTakeElseBranch(SourceLocation location, bool isElseIf, string_view macroName);

    // Handle parsing a branch of a conditional directive
    Trivia parseBranchDirective(Token directive, Token condition, bool taken);

    // TimeScale specifier parser
    bool expectTimeScaleSpecifier(Token& token, TimeScaleValue& value);

    // Specifies possible macro intrinsics.
    enum class MacroIntrinsic { None, Line, File };

    // A saved macro definition; if it came from source code, we will have a parsed
    // DefineDirectiveSyntax. Otherwise, it's an intrinsic macro and we'll note that here.
    struct MacroDef {
        DefineDirectiveSyntax* syntax = nullptr;
        MacroIntrinsic intrinsic = MacroIntrinsic::None;

        MacroDef() = default;
        MacroDef(DefineDirectiveSyntax* syntax) : syntax(syntax) {}
        MacroDef(MacroIntrinsic intrinsic) : intrinsic(intrinsic) {}

        bool valid() const { return syntax || intrinsic != MacroIntrinsic::None; }
        bool isIntrinsic() const { return intrinsic != MacroIntrinsic::None; }
        bool needsArgs() const;
    };

    // Helper class for tracking state used during expansion of a macro.
    class MacroExpansion {
    public:
        MacroExpansion(BumpAllocator& alloc, SmallVector<Token>& dest, Token usageSite,
                       bool isTopLevel) :
            alloc(alloc),
            dest(dest), usageSite(usageSite), isTopLevel(isTopLevel) {}

        SourceRange getRange() const;

        void append(Token token, SourceLocation location);

    private:
        BumpAllocator& alloc;
        SmallVector<Token>& dest;
        Token usageSite;
        bool any = false;
        bool isTopLevel = false;
    };

    // Macro handling methods
    MacroDef findMacro(Token directive);
    MacroActualArgumentListSyntax* handleTopLevelMacro(Token directive);
    bool expandMacro(MacroDef macro, MacroExpansion& expansion,
                     MacroActualArgumentListSyntax* actualArgs);
    bool expandIntrinsic(MacroIntrinsic intrinsic, MacroExpansion& expansion);
    bool expandReplacementList(span<Token const>& tokens,
                               SmallSet<DefineDirectiveSyntax*, 8>& alreadyExpanded);
    bool applyMacroOps(span<Token const> tokens, SmallVector<Token>& dest);

    // functions to advance the underlying token stream
    Token peek();
    Token consume();
    Token expect(TokenKind kind);
    bool peek(TokenKind kind) { return peek().kind == kind; }

    Diagnostic& addDiag(DiagCode code, SourceLocation location);

    // This is a small collection of state used to keep track of where we are in a tree of
    // nested conditional directives.
    struct BranchEntry {
        // Whether any of the sibling directives in this branch have been taken; used to decide
        // whether to take an `elsif or `else branch.
        bool anyTaken;

        // Whether the current branch is active.
        bool currentActive;

        // Has this chain of conditional directives had an `else directive yet; it's an error
        // for any other directives in the current level to come after that.
        bool hasElse = false;

        BranchEntry(bool taken) : anyTaken(taken), currentActive(taken) {}
    };

    // Helper class for parsing macro arguments. There's a lot of otherwise overlapping code that
    // this class consolidates, but it makes it a little confusing. If a buffer is provided via
    // setBuffer(), tokens are pulled from there first. Otherwise it just pulls from the main
    // preprocessor stream.
    class MacroParser {
    public:
        MacroParser(Preprocessor& preprocessor) : pp(preprocessor) {}

        // Set a buffer to use first, in order, before looking at an underlying preprocessor
        // stream for macro argument lists.
        void setBuffer(span<Token const> newBuffer);

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
        span<Token> parseTokenList(bool allowNewlines);

        Token peek();
        Token consume();
        Token expect(TokenKind kind);
        bool peek(TokenKind kind) { return peek().kind == kind; }

        Preprocessor& pp;
        span<Token const> buffer;
        uint32_t currentIndex = 0;
    };

    SourceManager& sourceManager;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    PreprocessorOptions options;
    LexerOptions lexerOptions;

    // stack of active lexers; each `include pushes a new lexer
    std::deque<Lexer*> lexerStack;

    // keep track of nested processor branches (ifdef, ifndef, else, elsif, endif)
    std::deque<BranchEntry> branchStack;

    // map from macro name to macro definition
    std::unordered_map<string_view, MacroDef> macros;

    // list of expanded macro tokens to drain before continuing with active lexer
    SmallVectorSized<Token, 16> expandedTokens;
    Token* currentMacroToken = nullptr;

    // the latest token pulled from a lexer
    Token currentToken;

    // the last token consumed before the currentToken; used to back up and
    // report errors in a different location in certain scenarios
    Token lastConsumed;

    // Directives don't get handled when lexing within a macro body
    // (either define or usage).
    bool inMacroBody = false;

    // A buffer used to hold tokens while we're busy consuming them for directives.
    SmallVectorSized<Token, 16> scratchTokenBuffer;

    /// Various state set by preprocessor directives.
    std::vector<KeywordVersion> keywordVersionStack;
    optional<TimeScale> activeTimeScale;
    TokenKind defaultNetType;
};

} // namespace slang
