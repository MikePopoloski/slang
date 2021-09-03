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
    PatternContext = 1 << 0,

    /// In a procedural assignment context, <= is a non-blocking assignment, not the less
    /// than or equal to operator.
    ProceduralAssignmentContext = 1 << 1,

    /// In a constraint block context, the -> operator has special meaning.
    ConstraintContext = 1 << 2,

    /// This expression is in a context where "super.new" calls are allowed.
    /// They are restricted to the first statement in a class constructor.
    AllowSuperNewCall = 1 << 3,

    /// This expression is inside a sequence expression.
    SequenceExpr = 1 << 4,

    /// When parsing a primary expression, don't parse a full integer vector
    /// but instead just the first integer literal token.
    DisallowVectors = 1 << 5,

    /// In a bins select context the && and || operators should be left
    /// to the bins parsing instead of being part of the expression itself.
    BinsSelectContext = 1 << 6
};
BITMASK(ExpressionOptions, BinsSelectContext);

/// Various options for parsing names.
enum class NameOptions {
    /// No special options specified.
    None = 0,

    /// Parsing the name of a foreach variable.
    ForeachName = 1 << 0,

    /// This is the first element of a potentially dotted name path.
    IsFirst = 1 << 1,

    /// The previous element in the name path was the 'this' keyword.
    PreviousWasThis = 1 << 2,

    /// The previous element in the name path was the 'local' keyword.
    PreviousWasLocal = 1 << 3,

    /// We are expecting an expression while parsing this name.
    ExpectingExpression = 1 << 4,

    /// This name is inside a sequence expression.
    SequenceExpr = 1 << 5
};
BITMASK(NameOptions, SequenceExpr);

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

/// Various options for parsing functions.
enum class FunctionOptions {
    /// No special options specified.
    None = 0,

    /// Allow tasks (as opposed to just functions).
    AllowTasks = 1,

    /// Allow formal argument names to be ommitted.
    AllowEmptyArgNames = 2,

    /// Allow the return type to be ommitted.
    AllowImplicitReturn = 4,

    /// The function header is for a prototype, so parsing rules
    /// are slightly different.
    IsPrototype = 8
};
BITMASK(FunctionOptions, AllowImplicitReturn);

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
    StatementSyntax& parseStatement(bool allowEmpty = true, bool allowSuperNew = false);
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

    /// Various metadata collected during parsing.
    struct Metadata {
        /// Collection of metadata that can be associated with a syntax node at parse time.
        struct Node {
            TokenKind defaultNetType;
            TokenKind unconnectedDrive;
            optional<TimeScale> timeScale;
        };

        /// Specific metadata that was in effect when certain syntax nodes were parsed
        /// (such as various bits of preprocessor state).
        flat_hash_map<const SyntaxNode*, Node> nodeMap;

        /// A set of names of all instantiations of global modules/interfaces/programs.
        /// This can be used to determine which modules should be considered as top-level
        /// roots of the design.
        flat_hash_set<string_view> globalInstances;

        /// A list of all names parsed that could represent a package or class name,
        /// since they are simple names that appear on the left-hand side of a double colon.
        SmallVectorSized<const IdentifierNameSyntax*, 4> classPackageNames;

        /// A list of all package import declarations parsed.
        SmallVectorSized<const PackageImportDeclarationSyntax*, 4> packageImports;

        /// A list of all defparams parsed.
        SmallVectorSized<const DefParamSyntax*, 4> defparams;

        /// A list of all class declarations parsed.
        SmallVectorSized<const ClassDeclarationSyntax*, 4> classDecls;

        /// A list of all bind directives parsed.
        SmallVectorSized<const BindDirectiveSyntax*, 4> bindDirectives;
    };

    /// Gets the current set of metadata collected during parsing.
    Metadata&& getMetadata() { return std::move(meta); }

private:
    using ExpressionOptions = detail::ExpressionOptions;
    using NameOptions = detail::NameOptions;
    using TypeOptions = detail::TypeOptions;
    using FunctionOptions = detail::FunctionOptions;
    using AttrList = span<AttributeInstanceSyntax*>;

    // ---- Recursive-descent parsing routines, by syntax type ----

    // clang-format off
    ExpressionSyntax& parseMinTypMaxExpression();
    ExpressionSyntax& parsePrimaryExpression(bitmask<ExpressionOptions> options);
    ExpressionSyntax& parseIntegerExpression(bool disallowVector);
    ExpressionSyntax& parseInsideExpression(ExpressionSyntax& expr);
    ExpressionSyntax& parsePostfixExpression(ExpressionSyntax& expr, bitmask<ExpressionOptions> options);
    ExpressionSyntax& parseNewExpression(NameSyntax& expr, bitmask<ExpressionOptions> options);
    ConcatenationExpressionSyntax& parseConcatenation(Token openBrace, ExpressionSyntax* first);
    StreamingConcatenationExpressionSyntax& parseStreamConcatenation(Token openBrace);
    StreamExpressionSyntax& parseStreamExpression();
    OpenRangeListSyntax& parseOpenRangeList();
    ExpressionSyntax& parseOpenRangeElement(bitmask<ExpressionOptions> options = {});
    ElementSelectSyntax& parseElementSelect();
    SelectorSyntax* parseElementSelector();
    NameSyntax& parseName(bitmask<NameOptions> options);
    NameSyntax& parseNamePart(bitmask<NameOptions> options);
    ParameterValueAssignmentSyntax* parseParameterValueAssignment();
    ArgumentListSyntax& parseArgumentList();
    ParamAssignmentSyntax& parseParamValue();
    ArgumentSyntax& parseArgument();
    PatternSyntax& parsePattern();
    StructurePatternMemberSyntax& parseMemberPattern();
    AssignmentPatternExpressionSyntax& parseAssignmentPatternExpression(DataTypeSyntax* type);
    AssignmentPatternItemSyntax& parseAssignmentPatternItem(ExpressionSyntax* key);
    EventExpressionSyntax& parseSignalEvent();
    EventExpressionSyntax& parseEventExpression();
    NamedBlockClauseSyntax* parseNamedBlockClause();
    TimingControlSyntax* parseTimingControl();
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
    StatementSyntax& parseRandSequenceStatement(NamedLabelSyntax* label, AttrList attributes);
    StatementSyntax& parseCheckerStatement(NamedLabelSyntax* label, AttrList attributes);
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
    PortHeaderSyntax& parsePortHeader(Token constKeyword, Token direction);
    PortDeclarationSyntax& parsePortDeclaration(AttrList attributes);
    TimeUnitsDeclarationSyntax& parseTimeUnitsDeclaration(AttrList attributes);
    span<PackageImportDeclarationSyntax*> parsePackageImports();
    PackageImportDeclarationSyntax& parseImportDeclaration(AttrList attributes);
    MemberSyntax& parseExportDeclaration(AttrList attributes);
    PackageImportItemSyntax& parsePackageImportItem();
    NetTypeDeclarationSyntax& parseNetTypeDecl(AttrList attributes);
    DPIImportSyntax& parseDPIImport(AttrList attributes);
    DPIExportSyntax& parseDPIExport(AttrList attributes);
    ElabSystemTaskSyntax* parseElabSystemTask(AttrList attributes);
    AssertionItemPortSyntax& parseAssertionItemPort(SyntaxKind parentKind);
    AssertionItemPortListSyntax* parseAssertionItemPortList(SyntaxKind parentKind);
    PropertyDeclarationSyntax& parsePropertyDeclaration(AttrList attributes);
    SequenceDeclarationSyntax& parseSequenceDeclaration(AttrList attributes);
    CheckerDeclarationSyntax& parseCheckerDeclaration(AttrList attributes);
    ParameterDeclarationBaseSyntax& parseParameterPort();
    ParameterDeclarationBaseSyntax& parseParameterDecl(Token keyword, Token* semi);
    TypeAssignmentSyntax& parseTypeAssignment();
    ClockingSkewSyntax* parseClockingSkew();
    MemberSyntax* parseClockingItem();
    MemberSyntax& parseClockingDeclaration(AttrList attributes);
    MemberSyntax& parseDefaultDisable(AttrList attributes);
    MemberSyntax& parseVariableDeclaration(AttrList attributes);
    DataDeclarationSyntax& parseDataDeclaration(AttrList attributes);
    LocalVariableDeclarationSyntax& parseLocalVariableDeclaration();
    MemberSyntax& parseNetDeclaration(AttrList attributes);
    DriveStrengthSyntax* parseDriveStrength();
    NetStrengthSyntax* parsePullStrength(Token type);
    TimingControlSyntax* parseDelay3();
    HierarchyInstantiationSyntax& parseHierarchyInstantiation(AttrList attributes);
    HierarchicalInstanceSyntax& parseHierarchicalInstance();
    PrimitiveInstantiationSyntax& parsePrimitiveInstantiation(AttrList attributes);
    CheckerInstantiationSyntax& parseCheckerInstantiation(AttrList attributes);
    PortConnectionSyntax& parsePortConnection();
    FunctionPortSyntax& parseFunctionPort(bool allowEmptyName);
    FunctionPortListSyntax* parseFunctionPortList(bool allowEmptyNames);
    FunctionPrototypeSyntax& parseFunctionPrototype(SyntaxKind parentKind, bitmask<FunctionOptions> options, bool* isConstructor = nullptr);
    FunctionDeclarationSyntax& parseFunctionDeclaration(AttrList attributes, SyntaxKind functionKind, TokenKind endKind, SyntaxKind parentKind);
    Token parseLifetime();
    span<SyntaxNode*> parseBlockItems(TokenKind endKind, Token& end, bool inConstructor);
    GenvarDeclarationSyntax& parseGenvarDeclaration(AttrList attributes);
    LoopGenerateSyntax& parseLoopGenerateConstruct(AttrList attributes);
    IfGenerateSyntax& parseIfGenerateConstruct(AttrList attributes);
    CaseGenerateSyntax& parseCaseGenerateConstruct(AttrList attributes);
    MemberSyntax& parseGenerateBlock();
    ImplementsClauseSyntax* parseImplementsClause(TokenKind keywordKind, Token& semi);
    ClassDeclarationSyntax& parseClassDeclaration(AttrList attributes, Token virtualOrInterface);
    MemberSyntax* parseClassMember(bool isIfaceClass);
    ContinuousAssignSyntax& parseContinuousAssign(AttrList attributes);
    DeclaratorSyntax& parseDeclarator(bool allowMinTypMax = false, bool requireInitializers = false);
    MemberSyntax* parseCoverageMember();
    BlockEventExpressionSyntax& parseBlockEventExpression();
    WithClauseSyntax* parseWithClause();
    CovergroupDeclarationSyntax& parseCovergroupDeclaration(AttrList attributes);
    CoverpointSyntax* parseCoverpoint(AttrList attributes, DataTypeSyntax* type, NamedLabelSyntax* label);
    CoverCrossSyntax* parseCoverCross(AttrList attributes, NamedLabelSyntax* label);
    CoverageOptionSyntax* parseCoverageOption(AttrList attributes);
    CoverageIffClauseSyntax* parseCoverageIffClause();
    MemberSyntax* parseCoverpointMember();
    MemberSyntax* parseCoverCrossMember();
    BinsSelectExpressionSyntax& parseBinsSelectPrimary();
    BinsSelectExpressionSyntax& parseBinsSelectExpression();
    MemberSyntax& parseConstraint(AttrList attributes, span<Token> qualifiers);
    ConstraintBlockSyntax& parseConstraintBlock(bool isTopLevel);
    ConstraintItemSyntax* parseConstraintItem(bool allowBlock, bool isTopLevel);
    DistConstraintListSyntax& parseDistConstraintList();
    DistItemSyntax& parseDistItem();
    ExpressionSyntax& parseArrayOrRandomizeMethod(ExpressionSyntax& expr);
    DefParamAssignmentSyntax& parseDefParamAssignment();
    DefParamSyntax& parseDefParam(AttrList attributes);
    ExpressionSyntax& parseExpressionOrDist(bitmask<ExpressionOptions> options = {});
    TransRangeSyntax& parseTransRange();
    TransSetSyntax& parseTransSet();
    TransListCoverageBinInitializerSyntax& parseTransListInitializer();
    ExpressionSyntax& parseSubExpression(bitmask<ExpressionOptions> options, int precedence);
    ExpressionSyntax& parseBinaryExpression(ExpressionSyntax* left, bitmask<ExpressionOptions> options, int precedence);
    BindDirectiveSyntax& parseBindDirective(AttrList attributes);
    UdpPortListSyntax& parseUdpPortList();
    UdpDeclarationSyntax& parseUdpDeclaration(AttrList attributes);
    UdpPortDeclSyntax& parseUdpPortDecl();
    UdpBodySyntax& parseUdpBody();
    UdpEntrySyntax& parseUdpEntry();
    SpecparamDeclaratorSyntax& parseSpecparamDeclarator();
    SpecparamDeclarationSyntax& parseSpecparam(AttrList attributes);
    MemberSyntax* parseSpecifyItem();
    SpecifyBlockSyntax& parseSpecifyBlock(AttrList attributes);
    NetAliasSyntax& parseNetAlias(AttrList attributes);
    PathDeclarationSyntax& parsePathDeclaration();
    SystemTimingCheckSyntax& parseSystemTimingCheck();
    TimingCheckArgSyntax& parseTimingCheckArg();
    EdgeDescriptorSyntax& parseEdgeDescriptor();
    SelectorSyntax* parseSequenceRange();
    SequenceExprSyntax& parseDelayedSequenceExpr(SequenceExprSyntax* first);
    SequenceExprSyntax& parseParenthesizedSeqExpr(Token openParen, SequenceExprSyntax& expr);
    SequenceExprSyntax& parseSequencePrimary();
    SequenceExprSyntax& parseSequenceExpr(int precedence, bool isInProperty);
    SequenceExprSyntax& parseBinarySequenceExpr(SequenceExprSyntax* left, int precedence, bool isInProperty);
    PropertyExprSyntax& parseCasePropertyExpr();
    PropertyExprSyntax& parsePropertyPrimary();
    PropertyExprSyntax& parsePropertyExpr(int precedence);
    SequenceMatchListSyntax* parseSequenceMatchList(Token& closeParen);
    SequenceRepetitionSyntax* parseSequenceRepetition();
    ProductionSyntax& parseProduction();
    RsRuleSyntax& parseRsRule();
    RsProdSyntax* parseRsProd();
    RsProdItemSyntax& parseRsProdItem();
    RsCodeBlockSyntax& parseRsCodeBlock();
    RsCaseSyntax& parseRsCase();
    // clang-format on

    template<bool (*IsEnd)(TokenKind)>
    span<TokenOrSyntax> parseDeclarators(TokenKind endKind, Token& end, bool allowMinTypMax = false,
                                         bool requireInitializers = false);
    span<TokenOrSyntax> parseDeclarators(Token& semi, bool allowMinTypMax = false,
                                         bool requireInitializers = false);

    template<typename TMember, typename TParseFunc>
    span<TMember*> parseMemberList(TokenKind endKind, Token& endToken, SyntaxKind parentKind,
                                   TParseFunc&& parseFunc);

    template<typename IsItemFunc, typename ParseItemFunc>
    bool parseCaseItems(TokenKind caseKind, SmallVector<CaseItemSyntax*>& itemBuffer,
                        IsItemFunc&& isItem, ParseItemFunc&& parseItem);

    span<TokenOrSyntax> parsePathTerminals();

    void checkClassQualifiers(span<const Token> qualifiers, bool isConstraint);
    Token parseDPISpecString();
    Token parseEdgeKeyword();

    // ---- Lookahead routines, for determining which kind of syntax to parse ----

    bool isPortDeclaration();
    bool isNetDeclaration();
    bool isVariableDeclaration();
    bool isLocalVariableDeclaration();
    bool isHierarchyInstantiation(bool requireName);
    bool isNonAnsiPort();
    bool isPlainPortName();
    bool isConditionalExpression();
    bool isSequenceRepetition();
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

    // Various metadata collected during parsing.
    Metadata meta;

    // Helper class for parsing out numeric literals.
    NumberParser numberParser;
    friend class NumberParser;

    // A stack of names of modules declared locally within the given scope.
    // This is used to detect and ignore instantiations of local modules when
    // trying to find the set of globally instantiated modules.
    SmallVectorSized<flat_hash_set<string_view>, 4> moduleDeclStack;

    // The current depth of recursion in the parser.
    size_t recursionDepth = 0;

    // The kind of definition currently being parsed, which could be a module,
    // interface, program, etc.
    SyntaxKind currentDefinitionKind = SyntaxKind::Unknown;

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
