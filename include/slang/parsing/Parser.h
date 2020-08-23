//------------------------------------------------------------------------------
//! @file Parser.h
//! @brief SystemVerilog language parser
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>

#include "slang/parsing/NumberParser.h"
#include "slang/parsing/ParserBase.h"
#include "slang/parsing/Token.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxFacts.h"
#include "slang/util/Bag.h"

namespace slang {

class Preprocessor;

namespace detail {

/// Various options for parsing expressions.
enum class ExpressionOptions {
    /// No special options specified.
    None = 0,

    /// Inside a pattern expression we don't allow a nested pattern expression.
    PatternContext = 1,

    /// In a procedural assignment context, <= is a non-blocking assignment, not the less
    /// than or equal to operator.
    ProceduralAssignmentContext = 2,

    /// In an event expression context, the "or" operator has special meaning.
    EventExpressionContext = 4,

    /// In a constraint block context, the -> operator has special meaning.
    ConstraintContext = 8
};
BITMASK(ExpressionOptions, ConstraintContext);

/// Various options for parsing names.
enum class NameOptions {
    /// No special options specified.
    None = 0,

    /// Parsing the name of a foreach variable.
    ForeachName = 1,

    /// This is the first element of a potentially dotted name path.
    IsFirst = 2,

    /// The previous element in the name path was the 'this' keyword.
    PreviousWasThis = 4,

    /// We are expecting an expression while parsing this name.
    ExpectingExpression = 8
};
BITMASK(NameOptions, ExpectingExpression);

/// Various options for parsing types.
enum class TypeOptions {
    /// No special options specified.
    None = 0,

    /// Allow implicit types, e.g. just a signing or dimension list.
    AllowImplicit = 1,

    /// Allow void types.
    AllowVoid = 2
};
BITMASK(TypeOptions, AllowVoid);

} // namespace detail

/// Contains various options that can control parsing behavior.
struct ParserOptions {
    /// The maximum depth of nested language constructs (statements, exceptions) before
    /// we give up for fear of stack overflow.
    uint32_t maxRecursionDepth = 1024;
};

/// Implements a full syntax parser for SystemVerilog.
class Parser : ParserBase, SyntaxFacts {
public:
    explicit Parser(Preprocessor& preprocessor, const Bag& options = {});

    /// Parse a whole compilation unit.
    CompilationUnitSyntax& parseCompilationUnit();

    /// Parse an expression / statement / module / class / name.
    /// These are mostly for testing; only use if you know that the
    /// source stream is currently looking at one of these.
    ExpressionSyntax& parseExpression();
    StatementSyntax& parseStatement(bool allowEmpty = true);
    ModuleDeclarationSyntax& parseModule();
    ClassDeclarationSyntax& parseClass();
    MemberSyntax* parseSingleMember(SyntaxKind parentKind);
    NameSyntax& parseName();

    /// Generalized node parse function that tries to figure out what we're
    /// looking at and parse that specifically. A normal batch compile won't call
    /// this, since in a well formed program every file is a compilation unit,
    /// but for snippets of code this can be convenient.
    SyntaxNode& parseGuess();

    /// Check whether the parser has consumed the entire input stream.
    bool isDone();

    /// Gets the EndOfFile token, if one has been consumed. Otherwise returns an empty token.
    Token getEOFToken();

    /// Collection of metadata that can be associated with a syntax node at parse time.
    struct NodeMetadata {
        TokenKind defaultNetType;
        TokenKind unconnectedDrive;
        optional<TimeScale> timeScale;
    };
    using MetadataMap = flat_hash_map<const SyntaxNode*, NodeMetadata>;

    /// Gets metadata that was in effect when certain syntax nodes were parsed (such as various
    /// bits of preprocessor state).
    MetadataMap&& getMetadataMap() { return std::move(metadataMap); }

    using NameSet = flat_hash_set<string_view>;

    /// Gets a set of names of all instantiations of global modules/interfaces/programs.
    /// This can be used to determine which modules should be considered as top-level
    /// roots of the design.
    NameSet&& getGlobalInstantiations() { return std::move(globalInstances); }

private:
    using ExpressionOptions = detail::ExpressionOptions;
    using NameOptions = detail::NameOptions;
    using TypeOptions = detail::TypeOptions;
    using AttrList = span<AttributeInstanceSyntax*>;

    // ---- Recursive-descent parsing routines, by syntax type ----

    // clang-format off
    ExpressionSyntax& parseMinTypMaxExpression();
    ExpressionSyntax& parsePrimaryExpression(bool disallowVector);
    ExpressionSyntax& parseIntegerExpression(bool disallowVector);
    ExpressionSyntax& parseInsideExpression(ExpressionSyntax& expr);
    ExpressionSyntax& parsePostfixExpression(ExpressionSyntax& expr);
    ExpressionSyntax& parseNewExpression(NameSyntax& expr);
    ConcatenationExpressionSyntax& parseConcatenation(Token openBrace, ExpressionSyntax* first);
    StreamingConcatenationExpressionSyntax& parseStreamConcatenation(Token openBrace);
    StreamExpressionSyntax& parseStreamExpression();
    OpenRangeListSyntax& parseOpenRangeList();
    ExpressionSyntax& parseOpenRangeElement();
    ElementSelectSyntax& parseElementSelect();
    SelectorSyntax* parseElementSelector();
    NameSyntax& parseName(bitmask<NameOptions> options);
    NameSyntax& parseNamePart(bitmask<NameOptions> options);
    ParameterValueAssignmentSyntax* parseParameterValueAssignment();
    ArgumentListSyntax& parseArgumentList(bool allowMinTypMax = false);
    ArgumentSyntax& parseArgument(bool allowMinTypMax);
    PatternSyntax& parsePattern();
    AssignmentPatternExpressionSyntax& parseAssignmentPatternExpression(DataTypeSyntax* type);
    AssignmentPatternItemSyntax& parseAssignmentPatternItem(ExpressionSyntax* key);
    EventExpressionSyntax& parseEventExpression();
    NamedBlockClauseSyntax* parseNamedBlockClause();
    TimingControlSyntax* parseTimingControl(bool isSequenceExpr);
    ConditionalPredicateSyntax& parseConditionalPredicate(ExpressionSyntax& first, TokenKind endKind, Token& end);
    ConditionalPatternSyntax& parseConditionalPattern();
    ConditionalStatementSyntax& parseConditionalStatement(NamedLabelSyntax* label, AttrList attributes, Token uniqueOrPriority);
    ElseClauseSyntax* parseElseClause();
    CaseStatementSyntax& parseCaseStatement(NamedLabelSyntax* label, AttrList attributes, Token uniqueOrPriority, Token caseKeyword);
    DefaultCaseItemSyntax& parseDefaultCaseItem();
    LoopStatementSyntax& parseLoopStatement(NamedLabelSyntax* label, AttrList attributes);
    DoWhileStatementSyntax& parseDoWhileStatement(NamedLabelSyntax* label, AttrList attributes);
    ForLoopStatementSyntax& parseForLoopStatement(NamedLabelSyntax* label, AttrList attributes);
    SyntaxNode& parseForInitializer();
    NameSyntax& parseForeachLoopVariable();
    ForeachLoopListSyntax& parseForeachLoopVariables();
    ForeachLoopStatementSyntax& parseForeachLoopStatement(NamedLabelSyntax* label, AttrList attributes);
    ReturnStatementSyntax& parseReturnStatement(NamedLabelSyntax* label, AttrList attributes);
    JumpStatementSyntax& parseJumpStatement(NamedLabelSyntax* label, AttrList attributes);
    ProceduralAssignStatementSyntax& parseProceduralAssignStatement(NamedLabelSyntax* label, AttrList attributes, SyntaxKind kind);
    ProceduralDeassignStatementSyntax& parseProceduralDeassignStatement(NamedLabelSyntax* label, AttrList attributes, SyntaxKind kind);
    StatementSyntax& parseDisableStatement(NamedLabelSyntax* label, AttrList attributes);
    StatementSyntax& parseAssertionStatement(NamedLabelSyntax* label, AttrList attributes);
    StatementSyntax& parseVoidCallStatement(NamedLabelSyntax* label, AttrList attributes);
    ConcurrentAssertionStatementSyntax& parseConcurrentAssertion(NamedLabelSyntax* label, AttrList attributes);
    PropertySpecSyntax& parsePropertySpec();
    ActionBlockSyntax& parseActionBlock();
    BlockStatementSyntax& parseBlock(SyntaxKind blockKind, TokenKind endKind, NamedLabelSyntax* label, AttrList attributes);
    StatementSyntax& parseWaitStatement(NamedLabelSyntax* label, AttrList attributes);
    WaitOrderStatementSyntax& parseWaitOrderStatement(NamedLabelSyntax* label, AttrList attributes);
    RandCaseStatementSyntax& parseRandCaseStatement(NamedLabelSyntax* label, AttrList attributes);
    EventTriggerStatementSyntax& parseEventTriggerStatement(NamedLabelSyntax* label, AttrList attributes);
    Token parseSigning();
    VariableDimensionSyntax* parseDimension();
    span<VariableDimensionSyntax*> parseDimensionList();
    StructUnionTypeSyntax& parseStructUnion(SyntaxKind syntaxKind);
    EnumTypeSyntax& parseEnum();
    DataTypeSyntax& parseDataType(bitmask<TypeOptions> options = {});
    DotMemberClauseSyntax* parseDotMemberClause();
    AttrList parseAttributes();
    AttributeSpecSyntax& parseAttributeSpec();
    MemberSyntax* parseMember(SyntaxKind parentKind, bool& anyLocalModules);
    ModuleHeaderSyntax& parseModuleHeader();
    ParameterPortListSyntax* parseParameterPortList();
    ModuleDeclarationSyntax& parseModule(AttrList attributes, SyntaxKind parentKind, bool& anyLocalModules);
    MemberSyntax& parseModportSubroutinePortList(AttrList attributes);
    MemberSyntax& parseModportPort();
    ModportItemSyntax& parseModportItem();
    ModportDeclarationSyntax& parseModportDeclaration(AttrList attributes);
    PortReferenceSyntax& parsePortReference();
    PortExpressionSyntax& parsePortExpression();
    NonAnsiPortSyntax& parseNonAnsiPort();
    MemberSyntax& parseAnsiPort();
    AnsiPortListSyntax& parseAnsiPortList(Token openParen);
    PortHeaderSyntax& parsePortHeader(Token direction);
    PortDeclarationSyntax& parsePortDeclaration(AttrList attributes);
    TimeUnitsDeclarationSyntax& parseTimeUnitsDeclaration(AttrList attributes);
    span<PackageImportDeclarationSyntax*> parsePackageImports();
    PackageImportDeclarationSyntax& parseImportDeclaration(AttrList attributes);
    PackageImportItemSyntax& parsePackageImportItem();
    NetTypeDeclarationSyntax& parseNetTypeDecl(AttrList attributes);
    DPIImportExportSyntax& parseDPIImportExport(AttrList attributes);
    ElabSystemTaskSyntax* parseElabSystemTask(AttrList attributes);
    AssertionItemPortListSyntax* parseAssertionItemPortList(TokenKind declarationKind);
    PropertyDeclarationSyntax& parsePropertyDeclaration(AttrList attributes);
    SequenceDeclarationSyntax& parseSequenceDeclaration(AttrList attributes);
    ParameterDeclarationBaseSyntax& parseParameterPort();
    ParameterDeclarationBaseSyntax& parseParameterDecl(Token keyword, Token* semi);
    TypeAssignmentSyntax& parseTypeAssignment();
    ClockingSkewSyntax* parseClockingSkew();
    MemberSyntax* parseClockingItem();
    MemberSyntax& parseClockingDeclaration(AttrList attributes);
    MemberSyntax& parseVariableDeclaration(AttrList attributes);
    MemberSyntax& parseNetDeclaration(AttrList attributes);
    DriveStrengthSyntax* parseDriveStrength();
    TimingControlSyntax* parseDelay3();
    HierarchyInstantiationSyntax& parseHierarchyInstantiation(AttrList attributes);
    HierarchicalInstanceSyntax& parseHierarchicalInstance();
    GateInstantiationSyntax& parseGateInstantiation(AttrList attributes);
    GateInstanceSyntax& parseGateInstance();
    PortConnectionSyntax& parsePortConnection();
    FunctionPortSyntax& parseFunctionPort();
    FunctionPrototypeSyntax& parseFunctionPrototype(bool allowTasks = true);
    FunctionDeclarationSyntax& parseFunctionDeclaration(AttrList attributes, SyntaxKind functionKind, TokenKind endKind);
    Token parseLifetime();
    span<SyntaxNode*> parseBlockItems(TokenKind endKind, Token& end);
    GenvarDeclarationSyntax& parseGenvarDeclaration(AttrList attributes);
    LoopGenerateSyntax& parseLoopGenerateConstruct(AttrList attributes);
    IfGenerateSyntax& parseIfGenerateConstruct(AttrList attributes);
    CaseGenerateSyntax& parseCaseGenerateConstruct(AttrList attributes);
    MemberSyntax& parseGenerateBlock();
    ImplementsClauseSyntax* parseImplementsClause(TokenKind keywordKind, Token& semi);
    ClassDeclarationSyntax& parseClassDeclaration(AttrList attributes, Token virtualOrInterface);
    MemberSyntax* parseClassMember();
    ContinuousAssignSyntax& parseContinuousAssign(AttrList attributes);
    DeclaratorSyntax& parseDeclarator(bool allowMinTypMax = false);
    MemberSyntax* parseCoverageMember();
    BlockEventExpressionSyntax& parseBlockEventExpression();
    WithClauseSyntax* parseWithClause();
    CovergroupDeclarationSyntax& parseCovergroupDeclaration(AttrList attributes);
    CoverpointSyntax* parseCoverpoint(AttrList attributes, DataTypeSyntax* type, NamedLabelSyntax* label);
    CoverageOptionSyntax* parseCoverageOption(AttrList attributes);
    MemberSyntax* parseCoverpointMember();
    MemberSyntax& parseConstraint(AttrList attributes, span<Token> qualifiers);
    ConstraintBlockSyntax& parseConstraintBlock();
    ConstraintItemSyntax* parseConstraintItem(bool allowBlock);
    DistConstraintListSyntax& parseDistConstraintList();
    DistItemSyntax& parseDistItem();
    ExpressionSyntax& parseArrayOrRandomizeMethod(ExpressionSyntax& expr);
    DefParamAssignmentSyntax& parseDefParamAssignment();
    DefParamSyntax& parseDefParam(AttrList attributes);
    ExpressionSyntax& parseExpressionOrDist();
    TransRangeSyntax& parseTransRange();
    TransSetSyntax& parseTransSet();
    TransListCoverageBinInitializerSyntax& parseTransListInitializer();
    ExpressionSyntax& parseSubExpression(bitmask<ExpressionOptions> options, int precedence);
    ExpressionSyntax& parsePrefixExpression(bitmask<ExpressionOptions> options, SyntaxKind opKind);
    // clang-format on

    template<bool (*IsEnd)(TokenKind)>
    span<TokenOrSyntax> parseDeclarators(TokenKind endKind, Token& end,
                                         bool allowMinTypMax = false);
    span<TokenOrSyntax> parseDeclarators(Token& semi, bool allowMinTypMax = false);

    template<typename TMember, typename TParseFunc>
    span<TMember*> parseMemberList(TokenKind endKind, Token& endToken, SyntaxKind parentKind,
                                   TParseFunc&& parseFunc);

    template<typename IsItemFunc, typename ParseItemFunc>
    bool parseCaseItems(TokenKind caseKind, SmallVector<CaseItemSyntax*>& itemBuffer,
                        IsItemFunc&& isItem, ParseItemFunc&& parseItem);

    span<Token> parseClassQualifiers(bool& isPureOrExtern);

    // ---- Lookahead routines, for determining which kind of syntax to parse ----

    bool isPortDeclaration();
    bool isNetDeclaration();
    bool isVariableDeclaration();
    bool isHierarchyInstantiation();
    bool isNonAnsiPort();
    bool isPlainPortName();
    bool isConditionalExpression();
    bool scanDimensionList(uint32_t& index);
    bool scanQualifiedName(uint32_t& index, bool allowNew);
    bool scanAttributes(uint32_t& index);

    template<bool (*IsEnd)(TokenKind)>
    bool scanTypePart(uint32_t& index, TokenKind start, TokenKind end);

    // ---- Stack recursion error detection ----

    class DepthGuard {
    public:
        DepthGuard(Parser& _parser) : parser(_parser) {
            if (++parser.recursionDepth > parser.parseOptions.maxRecursionDepth)
                parser.handleTooDeep();
        }
        ~DepthGuard() { --parser.recursionDepth; }

    private:
        Parser& parser;
    };
    DepthGuard setDepthGuard() { return DepthGuard(*this); }
    void handleTooDeep();

    class RecursionException : public std::runtime_error {
        using std::runtime_error::runtime_error;
    };

    // ---- Various helper methods ----

    // Reports an error if there are attributes in the given span.
    void errorIfAttributes(AttrList attributes);

    // Handle splitting out an exponent from a token that was otherwise miscategorized by the lexer.
    void handleExponentSplit(Token token, size_t offset);

    // Report errors for incorrectly specified block names.
    void checkBlockNames(string_view begin, string_view end, SourceLocation loc);
    void checkBlockNames(Token nameToken, const NamedBlockClauseSyntax* endBlock);
    void checkBlockNames(const NamedBlockClauseSyntax* beginBlock,
                         const NamedBlockClauseSyntax* endBlock, const NamedLabelSyntax* label);

    // Report errors for invalid members in specific kinds of blocks.
    void checkMemberAllowed(const SyntaxNode& member, SyntaxKind parentKind);

    // ---- Member variables ----

    // The factory used to create new syntax nodes.
    SyntaxFactory factory;

    // Stored parse options.
    ParserOptions parseOptions;

    // Map of metadata for previously parsed nodes.
    MetadataMap metadataMap;

    // Helper class for parsing out numeric literals.
    NumberParser numberParser;
    friend class NumberParser;

    // A stack of names of modules declared locally within the given scope.
    // This is used to detect and ignore instantiations of local modules when
    // trying to find the set of globally instantiated modules.
    SmallVectorSized<NameSet, 4> moduleDeclStack;

    // The names of all globally instantiated modules/interfaces/programs that
    // the parser has found. This is later used to determine which modules should
    // be considered as roots of the design.
    NameSet globalInstances;

    // The current depth of recursion in the parser.
    size_t recursionDepth = 0;

    // The held EOF token, if we've encountered it.
    Token eofToken;
};

template<bool (*IsEnd)(TokenKind)>
bool Parser::scanTypePart(uint32_t& index, TokenKind start, TokenKind end) {
    int nesting = 1;
    while (true) {
        auto kind = peek(index).kind;
        if (IsEnd(kind) || kind == TokenKind::EndOfFile)
            return false;

        index++;
        if (kind == start)
            nesting++;
        else if (kind == end) {
            nesting--;
            if (nesting <= 0)
                return true;
        }
    }
}

} // namespace slang
