//------------------------------------------------------------------------------
// Parser.h
// SystemVerilog language parser.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "AllSyntax.h"
#include "ArrayRef.h"
#include "ParserBase.h"
#include "Token.h"
#include "VectorBuilder.h"

namespace slang {

class BumpAllocator;
class Preprocessor;

/// Implements a full syntax parser for SystemVerilog.
class Parser : ParserBase {
public:
    static constexpr size_t MaxDepth=100;

    Parser(Preprocessor& preprocessor);

    /// Parse a whole compilation unit.
    CompilationUnitSyntax* parseCompilationUnit();

    /// Parse an expression / statement / module / class.
    /// These are mostly for testing; only use if you know that the
    /// source stream is currently looking at one of these.
    ExpressionSyntax* parseExpression();
    StatementSyntax* parseStatement(bool allowEmpty = true);
    ModuleDeclarationSyntax* parseModule();
    ClassDeclarationSyntax* parseClass();

private:
    ExpressionSyntax* parseMinTypMaxExpression();
    ExpressionSyntax* parsePrimaryExpression();
    ExpressionSyntax* parseIntegerExpression();
    ExpressionSyntax* parseInsideExpression(ExpressionSyntax* expr);
    ExpressionSyntax* parsePostfixExpression(ExpressionSyntax* expr);
    ExpressionSyntax* parseNewExpression();
    ConcatenationExpressionSyntax* parseConcatenation(Token openBrace, ExpressionSyntax* first);
    StreamingConcatenationExpressionSyntax* parseStreamConcatenation(Token openBrace);
    StreamExpressionSyntax* parseStreamExpression();
    OpenRangeListSyntax* parseOpenRangeList();
    ExpressionSyntax* parseOpenRangeElement();
    ElementSelectSyntax* parseElementSelect();
    SelectorSyntax* parseElementSelector();
    NameSyntax* parseName();
    NameSyntax* parseNamePart();
    ParameterValueAssignmentSyntax* parseParameterValueAssignment();
    ArgumentListSyntax* parseArgumentList();
    ArgumentSyntax* parseArgument();
    PatternSyntax* parsePattern();
    AssignmentPatternExpressionSyntax* parseAssignmentPatternExpression(DataTypeSyntax* type);
    AssignmentPatternItemSyntax* parseAssignmentPatternItem(ExpressionSyntax* key);
    EventExpressionSyntax* parseEventExpression();
    NamedBlockClauseSyntax* parseNamedBlockClause();
    TimingControlSyntax* parseTimingControl();
    ConditionalPredicateSyntax* parseConditionalPredicate(ExpressionSyntax* first, TokenKind endKind, Token& end);
    ConditionalPatternSyntax* parseConditionalPattern();
    ConditionalStatementSyntax* parseConditionalStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, Token uniqueOrPriority);
    ElseClauseSyntax* parseElseClause();
    CaseStatementSyntax* parseCaseStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, Token uniqueOrPriority, Token caseKeyword);
    DefaultCaseItemSyntax* parseDefaultCaseItem();
    LoopStatementSyntax* parseLoopStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    DoWhileStatementSyntax* parseDoWhileStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ForLoopStatementSyntax* parseForLoopStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    SyntaxNode* parseForInitializer();
    ForeachLoopListSyntax* parseForeachLoopVariables();
    ForeachLoopStatementSyntax* parseForeachLoopStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ReturnStatementSyntax* parseReturnStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    JumpStatementSyntax* parseJumpStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ProceduralAssignStatementSyntax* parseProceduralAssignStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind kind);
    ProceduralDeassignStatementSyntax* parseProceduralDeassignStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind kind);
    StatementSyntax* parseDisableStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    StatementSyntax* parseAssertionStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ConcurrentAssertionStatementSyntax* parseConcurrentAssertion(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    PropertySpecSyntax* parsePropertySpec();
    ActionBlockSyntax* parseActionBlock();
    BlockStatementSyntax* parseBlock(SyntaxKind blockKind, TokenKind endKind, NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    StatementSyntax* parseWaitStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    WaitOrderStatementSyntax* parseWaitOrderStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    RandCaseStatementSyntax* parseRandCaseStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    Token parseSigning();
    VariableDimensionSyntax* parseDimension();
    ArrayRef<VariableDimensionSyntax*> parseDimensionList();
    StructUnionTypeSyntax* parseStructUnion(SyntaxKind syntaxKind);
    EnumTypeSyntax* parseEnum();
    DataTypeSyntax* parseDataType(bool allowImplicit);
    DotMemberClauseSyntax* parseDotMemberClause();
    ArrayRef<AttributeInstanceSyntax*> parseAttributes();
    AttributeSpecSyntax* parseAttributeSpec();
    ModuleHeaderSyntax* parseModuleHeader();
    ParameterPortListSyntax* parseParameterPortList();
    ModuleDeclarationSyntax* parseModule(ArrayRef<AttributeInstanceSyntax*> attributes);
    NonAnsiPortSyntax* parseNonAnsiPort();
    AnsiPortSyntax* parseAnsiPort();
    AnsiPortListSyntax* parseAnsiPortList(Token openParen);
    PortHeaderSyntax* parsePortHeader(Token direction);
    PortDeclarationSyntax* parsePortDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    MemberSyntax* parseMember();
    TimeUnitsDeclarationSyntax* parseTimeUnitsDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    ArrayRef<PackageImportDeclarationSyntax*> parsePackageImports();
    PackageImportDeclarationSyntax* parseImportDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    PackageImportItemSyntax* parsePackageImportItem();
    ParameterDeclarationSyntax* parseParameterPort();
    MemberSyntax* parseVariableDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    MemberSyntax* parseNetDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    HierarchyInstantiationSyntax* parseHierarchyInstantiation(ArrayRef<AttributeInstanceSyntax*> attributes);
    HierarchicalInstanceSyntax* parseHierarchicalInstance();
    PortConnectionSyntax* parsePortConnection();
    FunctionPrototypeSyntax* parseFunctionPrototype();
    FunctionDeclarationSyntax* parseFunctionDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind functionKind, TokenKind endKind);
    Token parseLifetime();
    ArrayRef<SyntaxNode*> parseBlockItems(TokenKind endKind, Token& end);
    GenvarDeclarationSyntax* parseGenvarDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    LoopGenerateSyntax* parseLoopGenerateConstruct(ArrayRef<AttributeInstanceSyntax*> attributes);
    IfGenerateSyntax* parseIfGenerateConstruct(ArrayRef<AttributeInstanceSyntax*> attributes);
    CaseGenerateSyntax* parseCaseGenerateConstruct(ArrayRef<AttributeInstanceSyntax*> attributes);
    MemberSyntax* parseGenerateBlock();
    ImplementsClauseSyntax* parseImplementsClause(TokenKind keywordKind, Token& semi);
    ClassDeclarationSyntax* parseClassDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes, Token virtualOrInterface);
    MemberSyntax* parseClassMember();
    ContinuousAssignSyntax* parseContinuousAssign(ArrayRef<AttributeInstanceSyntax*> attributes);
    VariableDeclaratorSyntax* parseVariableDeclarator(bool isFirst);
    ArrayRef<TokenOrSyntax> parseOneVariableDeclarator();
    MemberSyntax* parseCoverageMember();
    BlockEventExpressionSyntax* parseBlockEventExpression();
    WithClauseSyntax* parseWithClause();
    CovergroupDeclarationSyntax* parseCovergroupDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    CoverpointSyntax* parseCoverpoint(ArrayRef<AttributeInstanceSyntax*> attributes, DataTypeSyntax* type, NamedLabelSyntax* label);
    CoverageOptionSyntax* parseCoverageOption(ArrayRef<AttributeInstanceSyntax*> attributes);
    MemberSyntax* parseCoverpointMember();
    MemberSyntax* parseConstraint(ArrayRef<AttributeInstanceSyntax*> attributes, ArrayRef<Token> qualifiers);
    ConstraintBlockSyntax* parseConstraintBlock();
    ConstraintItemSyntax* parseConstraintItem(bool allowBlock);
    DistConstraintListSyntax* parseDistConstraintList();
    DistItemSyntax* parseDistItem();
    ExpressionSyntax* parseArrayOrRandomizeWithClause();
    DefParamAssignmentSyntax* parseDefParamAssignment();
    DefParamSyntax* parseDefParam(ArrayRef<AttributeInstanceSyntax*> attributes);
    ExpressionSyntax* parseExpressionOrDist();

    bool isPortDeclaration();
    bool isNetDeclaration();
    bool isVariableDeclaration();
    bool isHierarchyInstantiation();
    bool isNonAnsiPort();
    bool isPlainPortName();
    bool scanDimensionList(int& index);
    bool scanQualifiedName(int& index);

    void errorIfAttributes(ArrayRef<AttributeInstanceSyntax*> attributes, const char* msg);

    class DepthGuard {
      public:
        DepthGuard(Parser &_parser)
            : parser(_parser) {
            ++parser.depth;
            parser.throwIfTooDeep();
        }
        ~DepthGuard() {
            --parser.depth;
        }
      private:
        Parser &parser;
    };
    DepthGuard setDepthGuard() {
        return DepthGuard(*this);
    }
    void throwIfTooDeep();

    /// Various options for parsing expressions.
    struct ExpressionOptions {
        enum Enum {
            None = 0,

            // Allow pattern matching expressions; these are not allowed recursively so
            // they're turned off after finding the first one
            AllowPatternMatch = 1,

            // In a procedural assignment context, <= is a non-blocking assignment, not less than or equals
            ProceduralAssignmentContext = 2,

            // In an event expression context, the "or" operator has special meaning
            EventExpressionContext = 4
        };
    };

    ExpressionSyntax* parseSubExpression(ExpressionOptions::Enum options, int precedence);
    ExpressionSyntax* parsePrefixExpression(ExpressionOptions::Enum options, SyntaxKind opKind);

    template<bool(*IsEnd)(TokenKind)>
    ArrayRef<TokenOrSyntax> parseVariableDeclarators(TokenKind endKind, Token& end);
    ArrayRef<TokenOrSyntax> parseVariableDeclarators(Token& semi);

    template<typename TMember, typename TParseFunc>
    ArrayRef<TMember*> parseMemberList(TokenKind endKind, Token& endToken, TParseFunc&& parseFunc);

    template<bool(*IsEnd)(TokenKind)>
    bool scanTypePart(int& index, TokenKind start, TokenKind end);

    // Scratch space for building up integer vector literals.
    VectorBuilder vectorBuilder;
    size_t depth = 0;
};

}
