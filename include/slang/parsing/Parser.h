//------------------------------------------------------------------------------
//! @file Parser.h
//! @brief SystemVerilog language parser
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/parsing/NumberParser.h"
#include "slang/parsing/ParserBase.h"
#include "slang/parsing/ParserMetadata.h"
#include "slang/parsing/Token.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxFacts.h"
#include "slang/util/Bag.h"
#include "slang/util/Hash.h"
#include "slang/util/LanguageVersion.h"

namespace slang::parsing {

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
    BinsSelectContext = 1 << 6,

    /// "dist" expressions are allowed in this context.
    AllowDist = 1 << 7,

    /// Attribute instances are disallowed in expression context.
    DisallowAttrs = 1 << 8
};
SLANG_BITMASK(ExpressionOptions, DisallowAttrs)

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
    SequenceExpr = 1 << 5,

    /// This name does not allow class scope components.
    NoClassScope = 1 << 6
};
SLANG_BITMASK(NameOptions, NoClassScope)

/// Various options for parsing types.
enum class TypeOptions {
    /// No special options specified.
    None = 0,

    /// Allow implicit types, e.g. just a signing or dimension list.
    AllowImplicit = 1,

    /// Allow void types.
    AllowVoid = 2
};
SLANG_BITMASK(TypeOptions, AllowVoid)

/// Various options for parsing functions.
enum class FunctionOptions {
    /// No special options specified.
    None = 0,

    /// Allow formal argument names to be ommitted.
    AllowEmptyArgNames = 1 << 0,

    /// Allow the return type to be ommitted.
    AllowImplicitReturn = 1 << 1,

    /// The function header is for a prototype, so parsing rules
    /// are slightly different.
    IsPrototype = 1 << 2,

    /// Allow use of the 'default' argument.
    AllowDefaultArg = 1 << 3,

    /// Allow override specifiers to be declared on the function prototype.
    AllowOverrideSpecifiers = 1 << 4
};
SLANG_BITMASK(FunctionOptions, AllowOverrideSpecifiers)

} // namespace detail

/// Contains various options that can control parsing behavior.
struct SLANG_EXPORT ParserOptions {
    /// The maximum depth of nested language constructs (statements, exceptions) before
    /// we give up for fear of stack overflow.
    uint32_t maxRecursionDepth = 1024;

    /// The version of the SystemVerilog language to use.
    LanguageVersion languageVersion = LanguageVersion::Default;
};

/// Implements a full syntax parser for SystemVerilog.
class SLANG_EXPORT Parser : ParserBase, syntax::SyntaxFacts {
public:
    explicit Parser(Preprocessor& preprocessor, const Bag& options = {});

    /// Parse a whole compilation unit.
    syntax::CompilationUnitSyntax& parseCompilationUnit();

    /// Parse a library map file.
    syntax::LibraryMapSyntax& parseLibraryMap();

    /// Parse an expression / statement / module / class / name.
    /// These are mostly for testing; only use if you know that the
    /// source stream is currently looking at one of these.
    syntax::ExpressionSyntax& parseExpression();
    syntax::StatementSyntax& parseStatement(bool allowEmpty = true, bool allowSuperNew = false);
    syntax::MemberSyntax& parseModule();
    syntax::ClassDeclarationSyntax& parseClass();
    syntax::MemberSyntax* parseSingleMember(syntax::SyntaxKind parentKind);
    syntax::NameSyntax& parseName();

    /// Generalized node parse function that tries to figure out what we're
    /// looking at and parse that specifically. A normal batch compile won't call
    /// this, since in a well formed program every file is a compilation unit,
    /// but for snippets of code this can be convenient.
    syntax::SyntaxNode& parseGuess();

    /// Check whether the parser has consumed the entire input stream.
    bool isDone();

    /// Gets the current set of metadata collected during parsing.
    ParserMetadata&& getMetadata();

private:
    using ExpressionOptions = detail::ExpressionOptions;
    using NameOptions = detail::NameOptions;
    using TypeOptions = detail::TypeOptions;
    using FunctionOptions = detail::FunctionOptions;
    using AttrList = std::span<syntax::AttributeInstanceSyntax*>;

    // ---- Recursive-descent parsing routines, by syntax type ----

    // clang-format off
    syntax::ExpressionSyntax& parseMinTypMaxExpression(bitmask<ExpressionOptions> options = {});
    syntax::ExpressionSyntax& parsePrimaryExpression(bitmask<ExpressionOptions> options);
    syntax::ExpressionSyntax& parseIntegerExpression(bool disallowVector);
    syntax::ExpressionSyntax& parseInsideExpression(syntax::ExpressionSyntax& expr);
    syntax::ExpressionSyntax& parsePostfixExpression(syntax::ExpressionSyntax& expr, bitmask<ExpressionOptions> options);
    syntax::ExpressionSyntax& parseNewExpression(syntax::NameSyntax& expr, bitmask<ExpressionOptions> options);
    syntax::ConcatenationExpressionSyntax& parseConcatenation(Token openBrace, syntax::ExpressionSyntax* first);
    syntax::StreamingConcatenationExpressionSyntax& parseStreamConcatenation(Token openBrace);
    syntax::StreamExpressionSyntax& parseStreamExpression();
    syntax::RangeListSyntax& parseRangeList();
    syntax::ExpressionSyntax& parseValueRangeElement(bitmask<ExpressionOptions> options = {});
    syntax::ElementSelectSyntax& parseElementSelect();
    syntax::SelectorSyntax* parseElementSelector();
    syntax::NameSyntax& parseName(bitmask<NameOptions> options);
    syntax::NameSyntax& parseNamePart(bitmask<NameOptions> options);
    syntax::ParameterValueAssignmentSyntax* parseParameterValueAssignment();
    syntax::ArgumentListSyntax& parseArgumentList();
    syntax::ParamAssignmentSyntax& parseParamValue();
    syntax::ArgumentSyntax& parseArgument();
    syntax::PatternSyntax& parsePattern();
    syntax::StructurePatternMemberSyntax& parseMemberPattern();
    syntax::AssignmentPatternExpressionSyntax& parseAssignmentPatternExpression(syntax::DataTypeSyntax* type);
    syntax::AssignmentPatternItemSyntax& parseAssignmentPatternItem(syntax::ExpressionSyntax* key);
    syntax::EventExpressionSyntax& parseSignalEvent();
    syntax::EventExpressionSyntax& parseEventExpression();
    syntax::NamedBlockClauseSyntax* parseNamedBlockClause();
    syntax::TimingControlSyntax* parseTimingControl();
    syntax::ConditionalPredicateSyntax& parseConditionalPredicate(syntax::ExpressionSyntax& first, TokenKind endKind, Token& end);
    syntax::ConditionalPatternSyntax& parseConditionalPattern();
    syntax::ConditionalStatementSyntax& parseConditionalStatement(syntax::NamedLabelSyntax* label, AttrList attributes, Token uniqueOrPriority);
    syntax::ElseClauseSyntax* parseElseClause();
    syntax::CaseStatementSyntax& parseCaseStatement(syntax::NamedLabelSyntax* label, AttrList attributes, Token uniqueOrPriority, Token caseKeyword);
    syntax::DefaultCaseItemSyntax& parseDefaultCaseItem();
    syntax::LoopStatementSyntax& parseLoopStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::DoWhileStatementSyntax& parseDoWhileStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::ForLoopStatementSyntax& parseForLoopStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::SyntaxNode& parseForInitializer();
    syntax::NameSyntax& parseForeachLoopVariable();
    syntax::ForeachLoopListSyntax& parseForeachLoopVariables();
    syntax::ForeachLoopStatementSyntax& parseForeachLoopStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::ReturnStatementSyntax& parseReturnStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::JumpStatementSyntax& parseJumpStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::ProceduralAssignStatementSyntax& parseProceduralAssignStatement(syntax::NamedLabelSyntax* label, AttrList attributes, syntax::SyntaxKind kind);
    syntax::ProceduralDeassignStatementSyntax& parseProceduralDeassignStatement(syntax::NamedLabelSyntax* label, AttrList attributes, syntax::SyntaxKind kind);
    syntax::StatementSyntax& parseDisableStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::StatementSyntax& parseAssertionStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::StatementSyntax& parseVoidCallStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::StatementSyntax& parseRandSequenceStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::StatementSyntax& parseCheckerStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::ConcurrentAssertionStatementSyntax& parseConcurrentAssertion(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::PropertySpecSyntax& parsePropertySpec();
    syntax::ActionBlockSyntax& parseActionBlock();
    syntax::BlockStatementSyntax& parseBlock(syntax::SyntaxKind blockKind, TokenKind endKind, syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::StatementSyntax& parseWaitStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::WaitOrderStatementSyntax& parseWaitOrderStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::RandCaseStatementSyntax& parseRandCaseStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    syntax::EventTriggerStatementSyntax& parseEventTriggerStatement(syntax::NamedLabelSyntax* label, AttrList attributes);
    Token parseSigning();
    syntax::VariableDimensionSyntax* parseDimension();
    std::span<syntax::VariableDimensionSyntax*> parseDimensionList();
    syntax::StructUnionTypeSyntax& parseStructUnion(syntax::SyntaxKind syntaxKind);
    syntax::EnumTypeSyntax& parseEnum();
    syntax::DataTypeSyntax& parseDataType(bitmask<TypeOptions> options = {});
    syntax::DotMemberClauseSyntax* parseDotMemberClause();
    AttrList parseAttributes();
    syntax::AttributeSpecSyntax& parseAttributeSpec();
    syntax::MemberSyntax* parseMember(syntax::SyntaxKind parentKind, bool& anyLocalModules);
    syntax::ModuleHeaderSyntax& parseModuleHeader();
    syntax::ParameterPortListSyntax* parseParameterPortList();
    syntax::MemberSyntax& parseModule(AttrList attributes, syntax::SyntaxKind parentKind, bool& anyLocalModules);
    syntax::AnonymousProgramSyntax& parseAnonymousProgram(AttrList attributes);
    syntax::MemberSyntax& parseModportSubroutinePortList(AttrList attributes);
    syntax::MemberSyntax& parseModportPort();
    syntax::ModportItemSyntax& parseModportItem();
    syntax::ModportDeclarationSyntax& parseModportDeclaration(AttrList attributes);
    syntax::PortReferenceSyntax& parsePortReference();
    syntax::PortExpressionSyntax& parsePortExpression();
    syntax::NonAnsiPortSyntax& parseNonAnsiPort();
    syntax::MemberSyntax& parseAnsiPort();
    syntax::AnsiPortListSyntax& parseAnsiPortList(Token openParen);
    syntax::PortHeaderSyntax& parsePortHeader(Token constKeyword, Token direction);
    syntax::PortDeclarationSyntax& parsePortDeclaration(AttrList attributes);
    syntax::TimeUnitsDeclarationSyntax& parseTimeUnitsDeclaration(AttrList attributes);
    std::span<syntax::PackageImportDeclarationSyntax*> parsePackageImports();
    syntax::PackageImportDeclarationSyntax& parseImportDeclaration(AttrList attributes);
    syntax::MemberSyntax& parseExportDeclaration(AttrList attributes);
    syntax::PackageImportItemSyntax& parsePackageImportItem();
    syntax::NetTypeDeclarationSyntax& parseNetTypeDecl(AttrList attributes);
    syntax::DPIImportSyntax& parseDPIImport(AttrList attributes);
    syntax::DPIExportSyntax& parseDPIExport(AttrList attributes);
    syntax::ElabSystemTaskSyntax* parseElabSystemTask(AttrList attributes);
    syntax::AssertionItemPortSyntax& parseAssertionItemPort(syntax::SyntaxKind parentKind);
    syntax::AssertionItemPortListSyntax* parseAssertionItemPortList(syntax::SyntaxKind parentKind);
    syntax::PropertyDeclarationSyntax& parsePropertyDeclaration(AttrList attributes);
    syntax::SequenceDeclarationSyntax& parseSequenceDeclaration(AttrList attributes);
    syntax::CheckerDeclarationSyntax& parseCheckerDeclaration(AttrList attributes);
    syntax::ParameterDeclarationBaseSyntax& parseParameterPort();
    syntax::ParameterDeclarationBaseSyntax& parseParameterDecl(Token keyword, Token* semi);
    syntax::TypeAssignmentSyntax& parseTypeAssignment();
    syntax::ClockingSkewSyntax* parseClockingSkew();
    syntax::MemberSyntax* parseClockingItem();
    syntax::MemberSyntax& parseClockingDeclaration(AttrList attributes);
    syntax::MemberSyntax& parseDefaultDisable(AttrList attributes);
    syntax::ForwardTypeRestrictionSyntax* parseTypeRestriction(bool isExpected);
    syntax::MemberSyntax& parseVariableDeclaration(AttrList attributes);
    syntax::DataDeclarationSyntax& parseDataDeclaration(AttrList attributes);
    syntax::LocalVariableDeclarationSyntax& parseLocalVariableDeclaration();
    syntax::MemberSyntax& parseNetDeclaration(AttrList attributes);
    syntax::DriveStrengthSyntax* parseDriveStrength();
    syntax::NetStrengthSyntax* parsePullStrength(Token type);
    syntax::TimingControlSyntax* parseDelay3();
    syntax::HierarchyInstantiationSyntax& parseHierarchyInstantiation(AttrList attributes);
    syntax::HierarchicalInstanceSyntax& parseHierarchicalInstance();
    syntax::PrimitiveInstantiationSyntax& parsePrimitiveInstantiation(AttrList attributes);
    syntax::CheckerInstantiationSyntax& parseCheckerInstantiation(AttrList attributes);
    syntax::PortConnectionSyntax& parsePortConnection();
    syntax::FunctionPortBaseSyntax& parseFunctionPort(bitmask<FunctionOptions> options);
    syntax::FunctionPortListSyntax* parseFunctionPortList(bitmask<FunctionOptions> options);
    syntax::FunctionPrototypeSyntax& parseFunctionPrototype(syntax::SyntaxKind parentKind, bitmask<FunctionOptions> options, bool* isConstructor = nullptr);
    syntax::FunctionDeclarationSyntax& parseFunctionDeclaration(AttrList attributes, syntax::SyntaxKind functionKind, TokenKind endKind, syntax::SyntaxKind parentKind, bitmask<FunctionOptions> options = {});
    std::span<syntax::ClassSpecifierSyntax*> parseClassSpecifierList(bool allowSpecifiers);
    Token parseLifetime();
    std::span<syntax::SyntaxNode*> parseBlockItems(TokenKind endKind, Token& end, bool inConstructor);
    syntax::GenvarDeclarationSyntax& parseGenvarDeclaration(AttrList attributes);
    syntax::LoopGenerateSyntax& parseLoopGenerateConstruct(AttrList attributes);
    syntax::IfGenerateSyntax& parseIfGenerateConstruct(AttrList attributes);
    syntax::CaseGenerateSyntax& parseCaseGenerateConstruct(AttrList attributes);
    syntax::MemberSyntax& parseGenerateBlock();
    syntax::ImplementsClauseSyntax* parseImplementsClause(TokenKind keywordKind, Token& semi);
    syntax::ClassSpecifierSyntax* parseClassSpecifier();
    syntax::ClassDeclarationSyntax& parseClassDeclaration(AttrList attributes, Token virtualOrInterface);
    syntax::MemberSyntax* parseClassMember(bool isIfaceClass, bool hasBaseClass);
    syntax::ContinuousAssignSyntax& parseContinuousAssign(AttrList attributes);
    syntax::DeclaratorSyntax& parseDeclarator(bool allowMinTypMax = false, bool requireInitializers = false);
    syntax::MemberSyntax* parseCoverageMember();
    syntax::BlockEventExpressionSyntax& parseBlockEventExpression();
    syntax::WithClauseSyntax* parseWithClause();
    syntax::CovergroupDeclarationSyntax& parseCovergroupDeclaration(AttrList attributes, bool inClass, bool hasBaseClass);
    syntax::CoverpointSyntax* parseCoverpoint(AttrList attributes, syntax::DataTypeSyntax* type, syntax::NamedLabelSyntax* label);
    syntax::CoverCrossSyntax* parseCoverCross(AttrList attributes, syntax::NamedLabelSyntax* label);
    syntax::CoverageOptionSyntax* parseCoverageOption(AttrList attributes);
    syntax::CoverageIffClauseSyntax* parseCoverageIffClause();
    syntax::MemberSyntax* parseCoverpointMember();
    syntax::MemberSyntax* parseCoverCrossMember();
    syntax::BinsSelectExpressionSyntax& parseBinsSelectPrimary();
    syntax::BinsSelectExpressionSyntax& parseBinsSelectExpression();
    syntax::MemberSyntax& parseConstraint(AttrList attributes, std::span<Token> qualifiers, bool hasBaseClass);
    syntax::ConstraintBlockSyntax& parseConstraintBlock(bool isTopLevel);
    syntax::ConstraintItemSyntax* parseConstraintItem(bool allowBlock, bool isTopLevel);
    syntax::DistConstraintListSyntax& parseDistConstraintList();
    syntax::DistItemBaseSyntax& parseDistItem();
    syntax::ExpressionSyntax& parseArrayOrRandomizeMethod(syntax::ExpressionSyntax& expr);
    syntax::DefParamAssignmentSyntax& parseDefParamAssignment();
    syntax::DefParamSyntax& parseDefParam(AttrList attributes);
    syntax::ExpressionSyntax& parseExpressionOrDist(bitmask<ExpressionOptions> options = {});
    syntax::TransRangeSyntax& parseTransRange();
    syntax::TransSetSyntax& parseTransSet();
    syntax::TransListCoverageBinInitializerSyntax& parseTransListInitializer();
    syntax::ExpressionSyntax& parseSubExpression(bitmask<ExpressionOptions> options, int precedence);
    syntax::ExpressionSyntax& parseBinaryExpression(syntax::ExpressionSyntax* left, bitmask<ExpressionOptions> options, int precedence);
    syntax::BindDirectiveSyntax& parseBindDirective(AttrList attributes);
    syntax::UdpPortListSyntax& parseUdpPortList(bool& isSequential);
    syntax::UdpDeclarationSyntax& parseUdpDeclaration(AttrList attributes);
    syntax::UdpPortDeclSyntax& parseUdpPortDecl(bool& isReg);
    syntax::UdpBodySyntax& parseUdpBody(bool isSequential);
    syntax::UdpFieldBaseSyntax* parseUdpField(bool required, bool isInput, bool isSequential, bool& sawTransition);
    syntax::UdpEntrySyntax& parseUdpEntry(bool isSequential);
    syntax::SpecparamDeclaratorSyntax& parseSpecparamDeclarator(syntax::SyntaxKind parentKind);
    syntax::SpecparamDeclarationSyntax& parseSpecparam(AttrList attributes, syntax::SyntaxKind parentKind);
    syntax::MemberSyntax* parseSpecifyItem();
    syntax::SpecifyBlockSyntax& parseSpecifyBlock(AttrList attributes);
    syntax::NetAliasSyntax& parseNetAlias(AttrList attributes);
    syntax::PathDeclarationSyntax& parsePathDeclaration();
    syntax::SystemTimingCheckSyntax& parseSystemTimingCheck();
    syntax::TimingCheckArgSyntax& parseTimingCheckArg();
    syntax::EdgeDescriptorSyntax& parseEdgeDescriptor();
    syntax::SelectorSyntax* parseSequenceRange();
    syntax::SequenceExprSyntax& parseDelayedSequenceExpr(syntax::SequenceExprSyntax* first);
    syntax::SequenceExprSyntax& parseParenthesizedSeqExpr(Token openParen, syntax::SequenceExprSyntax& expr);
    syntax::SequenceExprSyntax& parseSequencePrimary();
    syntax::SequenceExprSyntax& parseSequenceExpr(int precedence, bool isInProperty);
    syntax::SequenceExprSyntax& parseBinarySequenceExpr(syntax::SequenceExprSyntax* left, int precedence, bool isInProperty);
    syntax::PropertyExprSyntax& parseCasePropertyExpr();
    syntax::PropertyExprSyntax& parsePropertyPrimary();
    syntax::PropertyExprSyntax& parsePropertyExpr(int precedence);
    syntax::SequenceMatchListSyntax* parseSequenceMatchList(Token& closeParen);
    syntax::SequenceRepetitionSyntax* parseSequenceRepetition();
    syntax::ProductionSyntax& parseProduction();
    syntax::RsRuleSyntax& parseRsRule();
    syntax::RsProdSyntax* parseRsProd();
    syntax::RsProdItemSyntax& parseRsProdItem();
    syntax::RsCodeBlockSyntax& parseRsCodeBlock();
    syntax::RsCaseSyntax& parseRsCase();
    syntax::MemberSyntax* parseExternMember(syntax::SyntaxKind parentKind, AttrList attributes);
    syntax::ConfigCellIdentifierSyntax& parseConfigCellIdentifier();
    syntax::ConfigLiblistSyntax& parseConfigLiblist();
    syntax::ConfigUseClauseSyntax& parseConfigUseClause();
    syntax::ConfigDeclarationSyntax& parseConfigDeclaration(AttrList attributes);
    syntax::MemberSyntax* parseLibraryMember();
    syntax::FilePathSpecSyntax& parseFilePathSpec();
    syntax::LibraryDeclarationSyntax& parseLibraryDecl();
    // clang-format on

    template<bool (*IsEnd)(TokenKind)>
    std::span<syntax::TokenOrSyntax> parseDeclarators(TokenKind endKind, Token& end,
                                                      bool allowMinTypMax = false,
                                                      bool requireInitializers = false);
    std::span<syntax::TokenOrSyntax> parseDeclarators(Token& semi, bool allowMinTypMax = false,
                                                      bool requireInitializers = false);

    template<typename TMember, typename TParseFunc>
    std::span<TMember*> parseMemberList(TokenKind endKind, Token& endToken,
                                        syntax::SyntaxKind parentKind, TParseFunc&& parseFunc);

    template<typename IsItemFunc, typename ParseItemFunc>
    bool parseCaseItems(TokenKind caseKind, SmallVectorBase<syntax::CaseItemSyntax*>& itemBuffer,
                        IsItemFunc&& isItem, ParseItemFunc&& parseItem);

    std::span<syntax::TokenOrSyntax> parsePathTerminals();

    void checkClassQualifiers(std::span<const Token> qualifiers, bool isConstraint);
    Token parseDPISpecString();
    Token parseEdgeKeyword();

    // ---- Lookahead routines, for determining which kind of syntax to parse ----

    bool isMember();
    bool isPortDeclaration(bool inStatement);
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
    bool isStartOfAttrs(uint32_t index);

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
    void checkBlockNames(std::string_view begin, std::string_view end, SourceLocation loc);
    void checkBlockNames(Token nameToken, const syntax::NamedBlockClauseSyntax* endBlock);
    void checkBlockNames(const syntax::NamedBlockClauseSyntax* beginBlock,
                         const syntax::NamedBlockClauseSyntax* endBlock,
                         const syntax::NamedLabelSyntax* label);

    // Report errors for invalid members in specific kinds of blocks.
    void checkMemberAllowed(const syntax::SyntaxNode& member, syntax::SyntaxKind parentKind);

    // Report warnings for misleading empty loop / conditional bodies.
    void checkEmptyBody(const syntax::SyntaxNode& syntax, Token prevToken,
                        std::string_view syntaxName);

    // ---- Member variables ----

    // The factory used to create new syntax nodes.
    syntax::SyntaxFactory factory;

    // A pending node that should be stored as a "preview node"
    // on the next member that is parsed.
    const syntax::SyntaxNode* previewNode = nullptr;

    // Stored parse options.
    ParserOptions parseOptions;

    // Various metadata collected during parsing.
    ParserMetadata meta;

    // Helper class for parsing out numeric literals.
    NumberParser numberParser;
#ifndef __DOXYGEN__
    friend class NumberParser;
#endif

    // A stack of names of modules declared locally within the given scope.
    // This is used to detect and ignore instantiations of local modules when
    // trying to find the set of globally instantiated modules.
    SmallVector<flat_hash_set<std::string_view>, 4> moduleDeclStack;

    // The current depth of recursion in the parser.
    size_t recursionDepth = 0;

    // The kind of definition currently being parsed, which could be a module,
    // interface, program, etc.
    syntax::SyntaxKind currentDefinitionKind = syntax::SyntaxKind::Unknown;
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

} // namespace slang::parsing
