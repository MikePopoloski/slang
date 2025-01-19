//------------------------------------------------------------------------------
//! @file Preprocessor.h
//! @brief SystemVerilog preprocessor and directive support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <memory>

#include "slang/parsing/Lexer.h"
#include "slang/parsing/NumberParser.h"
#include "slang/parsing/Token.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Bag.h"
#include "slang/util/SmallVector.h"

namespace slang::syntax {

struct ConditionalDirectiveExpressionSyntax;
struct DefineDirectiveSyntax;
struct MacroActualArgumentListSyntax;
struct MacroFormalArgumentListSyntax;
struct MacroActualArgumentSyntax;
struct MacroFormalArgumentSyntax;
struct PragmaDirectiveSyntax;
struct PragmaExpressionSyntax;

} // namespace slang::syntax

namespace slang::parsing {

/// Contains various options that can control preprocessing behavior.
struct SLANG_EXPORT PreprocessorOptions {
    /// The maximum depth of the include stack; further attempts to include
    /// a file will result in an error.
    uint32_t maxIncludeDepth = 1024;

    /// The version of the SystemVerilog language to use.
    LanguageVersion languageVersion = LanguageVersion::Default;

    /// The name to associate with errors produced by macros specified
    /// via the @a predefines option.
    std::string predefineSource = "<api>";

    /// A set of macros to predefine, of the form &lt;macro>=&lt;value> or
    /// just &lt;macro> to predefine to a value of 1.
    std::vector<std::string> predefines;

    /// A set of macro names to undefine at the start of file preprocessing.
    std::vector<std::string> undefines;

    /// Additional include paths to use when preprocessing.
    std::vector<std::filesystem::path> additionalIncludePaths;

    /// A set of preprocessor directives to be ignored.
    flat_hash_set<std::string_view> ignoreDirectives;
};

/// Preprocessor - Interface between lexer and parser
///
/// This class handles the messy interface between various source file lexers, include directives,
/// and macro expansion, and the actual SystemVerilog parser that wants a nice coherent stream
/// of tokens to consume.
class SLANG_EXPORT Preprocessor {
public:
    Preprocessor(SourceManager& sourceManager, BumpAllocator& alloc, Diagnostics& diagnostics,
                 const Bag& options = {},
                 std::span<const syntax::DefineDirectiveSyntax* const> inheritedMacros = {});

    /// Gets the next token in the stream, after applying preprocessor rules.
    Token next();

    /// Push a new source file onto the stack.
    void pushSource(std::string_view source, std::string_view name = "source");
    void pushSource(SourceBuffer buffer);

    /// Predefines the given macro definition. The given definition string is lexed
    /// as if it were source text immediately following a @code `define @endcode directive.
    /// If any diagnostics are printed for the created text, they will be marked
    /// as coming from @a name.
    void predefine(const std::string& definition, std::string_view name = "<api>");

    /// Undefines a previously defined macro. If the macro is not defined, or
    /// if you pass the name of an intrinsic macro, this call returns false and
    /// does not undefine anything.
    bool undefine(std::string_view name);

    /// Undefines all currently defined macros.
    void undefineAll();

    /// Checks whether the given macro is defined. This does not check built-in
    /// directives except for the intrinsic macros (__LINE__, etc).
    bool isDefined(std::string_view name);

    /// Sets the base keyword version for the current compilation unit. Note that this does not
    /// affect the keyword version if the user has explicitly requested a different
    /// version via the begin_keywords directive.
    void setKeywordVersion(KeywordVersion version);

    /// Resets the state of all compiler directives; this is equivalent to encountering the
    /// @code `resetall @endcode directive in source. Note that this does not include the state
    /// of any macros that have been defined.
    void resetAllDirectives();

    /// Increases the preprocessor's view of the depth of parsed design elements,
    /// such as modules or interfaces. A parser calls this whenever starting to
    /// parse a new design element so that the preprocessor can enforce rules about
    /// where directives may appear.
    void pushDesignElementStack() { designElementDepth++; }

    /// Decreases the preprocessor's view of the depth of parsed design elements,
    /// such as modules or interfaces. A parser calls this whenever finishing
    /// parsing a design element so that the preprocessor can enforce rules about
    /// where directives may appear.
    void popDesignElementStack() { designElementDepth--; }

    /// Gets the currently active time scale value, if any has been set by the user.
    const std::optional<TimeScale>& getTimeScale() const { return activeTimeScale; }

    /// Gets the default net type to use if none is specified. This is set via
    /// the @code `default_nettype @endcode directive. If it is set to "none" by the user,
    /// this will return TokenKind::Unknown.
    TokenKind getDefaultNetType() const { return defaultNetType; }

    /// Gets the currently active drive strength to apply to unconnected nets,
    /// if any has been set by the user. If none is set, this returns TokenKind::Unknown.
    TokenKind getUnconnectedDrive() const { return unconnectedDrive; }

    /// Gets the currently active keyword version in use by the preprocessor.
    KeywordVersion getCurrentKeywordVersion() const { return keywordVersionStack.back(); }

    /// Gets the currently active source library, or nullptr if none has been set.
    const SourceLibrary* getCurrentLibrary() const;

    /// Gets the source manager associated with the preprocessor.
    SourceManager& getSourceManager() const { return sourceManager; }

    /// Gets the allocator used by the preprocessor.
    BumpAllocator& getAllocator() const { return alloc; }

    /// Gets the diagnostic bag passed to the Preprocessor's constructor.
    Diagnostics& getDiagnostics() const { return diagnostics; }

    /// Gets all macros that have been defined thus far in the preprocessor.
    std::vector<const syntax::DefineDirectiveSyntax*> getDefinedMacros() const;

private:
    Preprocessor(const Preprocessor& other);
    Preprocessor& operator=(const Preprocessor& other) = delete;

    // Internal methods to grab and handle the next token
    Token nextProcessed();
    Token nextRaw();
    void popSource();

    // directive handling methods
    Token handleDirectives(Token token);
    Trivia handleIncludeDirective(Token directive);
    Trivia handleResetAllDirective(Token directive);
    Trivia handleDefineDirective(Token directive);
    std::pair<Trivia, Trivia> handleMacroUsage(Token directive);
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
    Trivia handleUnconnectedDriveDirective(Token directive);
    Trivia handleNoUnconnectedDriveDirective(Token directive);
    Trivia handleDefaultDecayTimeDirective(Token directive);
    Trivia handleDefaultTriregStrengthDirective(Token directive);
    Trivia createSimpleDirective(Token directive);
    std::pair<Trivia, Trivia> handlePragmaDirective(Token directive);
    std::pair<Trivia, Trivia> handleProtectedDirective(Token directive);

    // Handle parsing a branch of a conditional directive
    syntax::ConditionalDirectiveExpressionSyntax* parseConditionalExpr();
    syntax::ConditionalDirectiveExpressionSyntax& parseConditionalExprTop();
    bool evalConditionalExpr(const syntax::ConditionalDirectiveExpressionSyntax& expr) const;
    bool shouldTakeElseBranch(SourceLocation location,
                              const syntax::ConditionalDirectiveExpressionSyntax* expr);
    Trivia parseBranchDirective(Token directive, syntax::ConditionalDirectiveExpressionSyntax* expr,
                                bool taken);

    // TimeScale specifier parser
    bool expectTimeScaleSpecifier(Token& token, TimeScaleValue& value);

    // Reports an error if the given directive occurred inside a design element.
    void checkOutsideDesignElement(Token directive);

    // Pragma expression parsers
    std::pair<syntax::PragmaExpressionSyntax*, bool> parsePragmaExpression();
    std::pair<syntax::PragmaExpressionSyntax*, bool> parsePragmaValue();
    std::pair<syntax::PragmaExpressionSyntax*, bool> checkNextPragmaToken();

    // Pragma action handlers
    void applyPragma(const syntax::PragmaDirectiveSyntax& pragma,
                     SmallVectorBase<Token>& skippedTokens);
    void applyProtectPragma(const syntax::PragmaDirectiveSyntax& pragma,
                            SmallVectorBase<Token>& skippedTokens);
    void applyResetPragma(const syntax::PragmaDirectiveSyntax& pragma);
    void applyResetAllPragma(const syntax::PragmaDirectiveSyntax& pragma);
    void applyOncePragma(const syntax::PragmaDirectiveSyntax& pragma);
    void applyDiagnosticPragma(const syntax::PragmaDirectiveSyntax& pragma);
    void ensurePragmaArgs(const syntax::PragmaDirectiveSyntax& pragma, size_t count);
    void ensureNoPragmaArgs(Token keyword, const syntax::PragmaExpressionSyntax* args);
    void resetProtectState();

    // Pragma protect handlers
    void handleProtectBegin(Token keyword, const syntax::PragmaExpressionSyntax* args,
                            SmallVectorBase<Token>& skippedTokens);
    void handleProtectEnd(Token keyword, const syntax::PragmaExpressionSyntax* args,
                          SmallVectorBase<Token>& skippedTokens);
    void handleProtectBeginProtected(Token keyword, const syntax::PragmaExpressionSyntax* args,
                                     SmallVectorBase<Token>& skippedTokens);
    void handleProtectEndProtected(Token keyword, const syntax::PragmaExpressionSyntax* args,
                                   SmallVectorBase<Token>& skippedTokens);
    void handleProtectSingleArgIgnore(Token keyword, const syntax::PragmaExpressionSyntax* args,
                                      SmallVectorBase<Token>& skippedTokens);
    void handleProtectEncoding(Token keyword, const syntax::PragmaExpressionSyntax* args,
                               SmallVectorBase<Token>& skippedTokens);
    void handleProtectKey(Token keyword, const syntax::PragmaExpressionSyntax* args,
                          SmallVectorBase<Token>& skippedTokens);
    void handleProtectBlock(Token keyword, const syntax::PragmaExpressionSyntax* args,
                            SmallVectorBase<Token>& skippedTokens);
    void handleProtectLicense(Token keyword, const syntax::PragmaExpressionSyntax* args,
                              SmallVectorBase<Token>& skippedTokens);
    void handleProtectReset(Token keyword, const syntax::PragmaExpressionSyntax* args,
                            SmallVectorBase<Token>& skippedTokens);
    void handleProtectViewport(Token keyword, const syntax::PragmaExpressionSyntax* args,
                               SmallVectorBase<Token>& skippedTokens);
    void handleEncryptedRegion(Token keyword, const syntax::PragmaExpressionSyntax* args,
                               SmallVectorBase<Token>& skippedTokens, bool isSingleLine);

    // Pragma helpers
    std::optional<uint32_t> requireUInt32(const syntax::PragmaExpressionSyntax& expr);
    void skipMacroTokensBeforeProtectRegion(Token directive, SmallVectorBase<Token>& skippedTokens);

    // Specifies possible macro intrinsics.
    enum class MacroIntrinsic { None, Line, File };

    // A saved macro definition; if it came from source code, we will have a parsed
    // DefineDirectiveSyntax. Otherwise, it's an intrinsic macro and we'll note that here.
    struct MacroDef {
        const syntax::DefineDirectiveSyntax* syntax = nullptr;
        MacroIntrinsic intrinsic = MacroIntrinsic::None;
        bool builtIn = false;
        bool commandLine = false;

        MacroDef() = default;
        MacroDef(const syntax::DefineDirectiveSyntax* syntax) : syntax(syntax) {}
        MacroDef(MacroIntrinsic intrinsic) : intrinsic(intrinsic), builtIn(true) {}

        bool valid() const { return syntax || intrinsic != MacroIntrinsic::None; }
        bool isIntrinsic() const { return intrinsic != MacroIntrinsic::None; }
        bool needsArgs() const;
    };

    // Helper class for tracking state used during expansion of a macro.
    class MacroExpansion {
    public:
        MacroExpansion(SourceManager& sourceManager, BumpAllocator& alloc,
                       SmallVectorBase<Token>& dest, Token usageSite, bool isTopLevel) :
            sourceManager(sourceManager), alloc(alloc), dest(dest), usageSite(usageSite),
            isTopLevel(isTopLevel) {}

        SourceRange getRange() const;

        SourceLocation adjustLoc(Token token, SourceLocation& macroLoc, SourceLocation& firstLoc,
                                 SourceRange expansionRange) const;

        void append(Token token, SourceLocation location, bool allowLineContinuation = false);
        void append(Token token, SourceLocation& macroLoc, SourceLocation& firstLoc,
                    SourceRange expansionRange, bool allowLineContinuation = false);

    private:
        SourceManager& sourceManager;
        BumpAllocator& alloc;
        SmallVectorBase<Token>& dest;
        Token usageSite;
        bool any = false;
        bool isTopLevel = false;
    };

    // Macro handling methods
    MacroDef findMacro(Token directive);
    std::pair<syntax::MacroActualArgumentListSyntax*, Trivia> handleTopLevelMacro(Token directive);
    bool expandMacro(MacroDef macro, MacroExpansion& expansion,
                     syntax::MacroActualArgumentListSyntax* actualArgs);
    bool expandIntrinsic(MacroIntrinsic intrinsic, MacroExpansion& expansion);
    bool expandReplacementList(std::span<Token const>& tokens,
                               SmallSet<const syntax::DefineDirectiveSyntax*, 8>& alreadyExpanded);
    bool applyMacroOps(std::span<Token const> tokens, SmallVectorBase<Token>& dest);
    void createBuiltInMacro(std::string_view name, int value, std::string_view valueStr = {});
    void splitTokens(Token sourceToken, size_t offset, SmallVectorBase<Token>& results);
    Token getLastConsumed() const { return lastConsumed; }

    static bool isSameMacro(const syntax::DefineDirectiveSyntax& left,
                            const syntax::DefineDirectiveSyntax& right);

    // functions to advance the underlying token stream
    Token peek();
    Token consume();
    Token expect(TokenKind kind);
    bool peek(TokenKind kind) { return peek().kind == kind; }
    bool peekSameLine() const;

    Diagnostic& addDiag(DiagCode code, SourceLocation location);
    Diagnostic& addDiag(DiagCode code, SourceRange range);

    // This is a small collection of state used to keep track of where we are in a tree of
    // nested conditional directives.
    struct BranchEntry {
        Token directive;

        // Whether any of the sibling directives in this branch have been taken; used to decide
        // whether to take an elsif or else branch.
        bool anyTaken;

        // Whether the current branch is active.
        bool currentActive;

        // Has this chain of conditional directives had an else directive yet; it's an error
        // for any other directives in the current level to come after that.
        bool hasElse = false;

        BranchEntry(Token directive, bool taken) :
            directive(directive), anyTaken(taken), currentActive(taken) {}
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
        void setBuffer(std::span<Token const> newBuffer);

        // Pull tokens one at a time from a previously set buffer. Note that this won't pull
        // from the underlying preprocessor stream; its purpose is to allow stepping through
        // a macro replacement list.
        Token next();

        syntax::MacroActualArgumentListSyntax* parseActualArgumentList(Token prevToken);
        syntax::MacroFormalArgumentListSyntax* parseFormalArgumentList();

    private:
        template<typename TFunc>
        void parseArgumentList(SmallVectorBase<syntax::TokenOrSyntax>& buffer, TFunc&& parseItem,
                               Token& closeParen);

        syntax::MacroActualArgumentSyntax* parseActualArgument();
        syntax::MacroFormalArgumentSyntax* parseFormalArgument();
        std::span<Token> parseTokenList(bool allowNewlines);

        Token peek();
        Token consume();
        Token expect(TokenKind kind);
        bool peek(TokenKind kind) { return peek().kind == kind; }

        Preprocessor& pp;
        std::span<Token const> buffer;
        uint32_t currentIndex = 0;
    };

    SourceManager& sourceManager;
    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    PreprocessorOptions options;
    LexerOptions lexerOptions;

    // stack of active lexers; each include pushes a new lexer
    SmallVector<std::unique_ptr<Lexer>, 2> lexerStack;

    // keep track of nested processor branches (ifdef, ifndef, else, elsif, endif)
    SmallVector<BranchEntry, 2> branchStack;

    // map from macro name to macro definition
    flat_hash_map<std::string_view, MacroDef> macros;

    // list of expanded macro tokens to drain before continuing with active lexer
    SmallVector<Token> expandedTokens;
    Token* currentMacroToken = nullptr;

    // the latest token pulled from a lexer
    Token currentToken;

    // the last token consumed before the currentToken; used to back up and
    // report errors in a different location in certain scenarios
    Token lastConsumed;

    // Directives don't get handled when lexing within a macro body
    // (either define or usage).
    bool inMacroBody = false;

    // Special handling for pulling directives when in an ifdef condition expr.
    bool inIfDefCondition = false;

    // A buffer used to hold tokens while we're busy consuming them for directives.
    SmallVector<Token> scratchTokenBuffer;

    // A set of files (identified by a pointer to the start of their text buffer) that
    // have been marked pragma once so that we avoid trying to include them more than once.
    flat_hash_set<const char*> includeOnceHeaders;

    /// Various state set by preprocessor directives.
    std::vector<KeywordVersion> keywordVersionStack;
    std::optional<TimeScale> activeTimeScale;
    TokenKind defaultNetType = TokenKind::WireKeyword;
    TokenKind unconnectedDrive = TokenKind::Unknown;

    int designElementDepth = 0;
    uint32_t includeDepth = 0;
    uint32_t protectEncryptDepth = 0;
    uint32_t protectDecryptDepth = 0;
    uint32_t protectLineLength = 0;
    uint32_t protectBytes = 0;
    ProtectEncoding protectEncoding = ProtectEncoding::Raw;

    // Parser for numeric literals in pragma expressions.
    NumberParser numberParser;
#ifndef __DOXYGEN__
    friend class NumberParser;
#endif

    // Called by NumberParser to handle an error condition.
    void handleExponentSplit(Token token, size_t offset);

    // A map of pragma protect keywords to their handler function.
    flat_hash_map<std::string_view,
                  void (Preprocessor::*)(Token, const syntax::PragmaExpressionSyntax*,
                                         SmallVectorBase<Token>&)>
        pragmaProtectHandlers;
};

} // namespace slang::parsing
