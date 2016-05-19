#pragma once

#include "AllSyntax.h"
#include "ArrayRef.h"
#include "ParserBase.h"
#include "Token.h"

namespace slang {

class BumpAllocator;
class Preprocessor;

class Parser : ParserBase {
public:
    Parser(Preprocessor& preprocessor);

    CompilationUnitSyntax* parseCompilationUnit();

    ExpressionSyntax* parseExpression();
    StatementSyntax* parseStatement();
    ModuleDeclarationSyntax* parseModule();

private:
    ExpressionSyntax* parseMinTypMaxExpression();
    ExpressionSyntax* parsePrimaryExpression();
    ExpressionSyntax* parseIntegerExpression();
    ExpressionSyntax* parseInsideExpression(ExpressionSyntax* expr);
    ExpressionSyntax* parsePostfixExpression(ExpressionSyntax* expr);
    ConcatenationExpressionSyntax* parseConcatenation(Token* openBrace, ExpressionSyntax* first);
    StreamingConcatenationExpressionSyntax* parseStreamConcatenation(Token* openBrace);
    StreamExpressionSyntax* parseStreamExpression();
    ExpressionSyntax* parseInsideElement();
    ElementSelectSyntax* parseElementSelect();
    SelectorSyntax* parseElementSelector();
    NameSyntax* parseName();
    NameSyntax* parseNamePart();
    ParameterValueAssignmentSyntax* parseParameterValueAssignment();
    ArgumentListSyntax* parseArgumentList();
    ArgumentSyntax* parseArgument();
    PatternSyntax* parsePattern();
    EventExpressionSyntax* parseEventExpression();
    NamedBlockClauseSyntax* parseNamedBlockClause();
    TimingControlSyntax* parseTimingControl(bool allowRepeat);
    ConditionalPredicateSyntax* parseConditionalPredicate(ExpressionSyntax* first, TokenKind endKind, Token*& end);
    ConditionalPatternSyntax* parseConditionalPattern();
    ConditionalStatementSyntax* parseConditionalStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, Token* uniqueOrPriority);
    ElseClauseSyntax* parseElseClause();
    CaseStatementSyntax* parseCaseStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, Token* uniqueOrPriority, Token* caseKeyword);
    DefaultCaseItemSyntax* parseDefaultCaseItem();
    LoopStatementSyntax* parseLoopStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    DoWhileStatementSyntax* parseDoWhileStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ForLoopStatementSyntax* parseForLoopStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ForInitializerSyntax* parseForInitializer();
    VariableAssignmentSyntax* parseVariableAssignment();
    ForeachLoopStatementSyntax* parseForeachLoopStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ReturnStatementSyntax* parseReturnStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    JumpStatementSyntax* parseJumpStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    AssignmentStatementSyntax* parseAssignmentStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ProceduralAssignStatementSyntax* parseProceduralAssignStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind kind);
    ProceduralDeassignStatementSyntax* parseProceduralDeassignStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind kind);
    StatementSyntax* parseDisableStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ImmediateAssertionStatementSyntax* parseAssertionStatement(SyntaxKind assertionKind, NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    ActionBlockSyntax* parseActionBlock();
    SequentialBlockStatementSyntax* parseSequentialBlock(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    StatementSyntax* parseWaitStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    WaitOrderStatementSyntax* parseWaitOrderStatement(NamedLabelSyntax* label, ArrayRef<AttributeInstanceSyntax*> attributes);
    Token* parseSigning();
    VariableDimensionSyntax* parseDimension();
    ArrayRef<VariableDimensionSyntax*> parseDimensionList();
    StructUnionTypeSyntax* parseStructUnion(SyntaxKind syntaxKind);
    EnumTypeSyntax* parseEnum();
    DataTypeSyntax* parseDataType(bool allowImplicit);
    DotMemberClauseSyntax* parseDotMemberClause();
    ArrayRef<AttributeInstanceSyntax*> parseAttributes();
    AttributeSpecSyntax* parseAttributeSpec();
    ModuleHeaderSyntax* parseModuleHeader();
    ModuleDeclarationSyntax* parseModule(ArrayRef<AttributeInstanceSyntax*> attributes);
    NonAnsiPortSyntax* parseNonAnsiPort();
    AnsiPortSyntax* parseAnsiPort();
    AnsiPortListSyntax* parseAnsiPortList(Token* openParen);
    PortHeaderSyntax* parsePortHeader(Token* direction);
    PortDeclarationSyntax* parsePortDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    MemberSyntax* parseMember();
    ArrayRef<MemberSyntax*> parseMemberList(TokenKind endKind, Token*& endToken);
    TimeUnitsDeclarationSyntax* parseTimeUnitsDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    ArrayRef<PackageImportDeclarationSyntax*> parsePackageImports();
    PackageImportItemSyntax* parsePackageImportItem();
    ParameterPortDeclarationSyntax* parseParameterPort();
    MemberSyntax* parseVariableDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    MemberSyntax* parseNetDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    HierarchyInstantiationSyntax* parseHierarchyInstantiation(ArrayRef<AttributeInstanceSyntax*> attributes);
    HierarchicalInstanceSyntax* parseHierarchicalInstance();
    PortConnectionSyntax* parsePortConnection();
    FunctionDeclarationSyntax* parseFunctionDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes, SyntaxKind functionKind, TokenKind endKind);
    Token* parseLifetime();
    ArrayRef<SyntaxNode*> parseBlockItems(TokenKind endKind, Token*& end);
    GenvarDeclarationSyntax* parseGenvarDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes);
    LoopGenerateSyntax* parseLoopGenerateConstruct(ArrayRef<AttributeInstanceSyntax*> attributes);
    IfGenerateSyntax* parseIfGenerateConstruct(ArrayRef<AttributeInstanceSyntax*> attributes);
    CaseGenerateSyntax* parseCaseGenerateConstruct(ArrayRef<AttributeInstanceSyntax*> attributes);
    MemberSyntax* parseGenerateBlock();
    ClassDeclarationSyntax* parseClassDeclaration(ArrayRef<AttributeInstanceSyntax*> attributes, Token* virtualOrInterface);
    ContinuousAssignSyntax* parseContinuousAssign(ArrayRef<AttributeInstanceSyntax*> attributes);

    bool isPortDeclaration();
    bool isNetDeclaration();
    bool isVariableDeclaration();
    bool isHierarchyInstantiation();
    bool isNonAnsiPort();
    bool isPlainPortName();
    bool scanDimensionList(int& index);
    bool scanQualifiedName(int& index);

    bool checkVectorDigits(Token* token);

    template<bool AllowPatternMatch>
    ExpressionSyntax* parseSubExpression(int precedence);

    template<bool(*IsEnd)(TokenKind)>
    ArrayRef<TokenOrSyntax> parseVariableDeclarators(TokenKind endKind, Token*& end);
    ArrayRef<TokenOrSyntax> parseVariableDeclarators(Token*& semi);

    template<bool AllowMinTypMax>
    VariableDeclaratorSyntax* parseVariableDeclarator(bool isFirst);
    ArrayRef<TokenOrSyntax> parseOneVariableDeclarator();

    template<bool AllowMinTypeMax>
    ExpressionSyntax* parseAssignmentExpression();

    template<bool(*IsEnd)(TokenKind)>
    bool scanTypePart(int& index, TokenKind start, TokenKind end);
};

}
