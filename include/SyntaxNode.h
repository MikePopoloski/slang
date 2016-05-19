#pragma once

#include <cmath>
#include <cstdint>
#include <cstddef>
#include <string>

#include "ArrayRef.h"
#include "Buffer.h"

namespace slang {

class Token;
class SyntaxNode;

enum class SyntaxKind : uint16_t {
    Unknown,
    List,

    // directives
    BeginKeywordsDirective,
    CellDefineDirective,
    DefaultNetTypeDirective,
    DefineDirective,
    ElseDirective,
    ElseIfDirective,
    EndKeywordsDirective,
    EndCellDefineDirective,
    EndIfDirective,
    IfDefDirective,
    IfNDefDirective,
    IncludeDirective,
    LineDirective,
    NoUnconnectedDriveDirective,
    PragmaDirective,
    ResetAllDirective,
    TimescaleDirective,
    UnconnectedDriveDirective,
    UndefDirective,
    UndefineAllDirective,

    // macros
    MacroUsage,
    MacroFormalArgumentList,
    MacroFormalArgument,
    MacroArgumentDefault,
    MacroActualArgumentList,
    MacroActualArgument,

    // attributes
    AttributeSpec,
    AttributeInstance,

    // arguments
    OrderedArgument,
    NamedArgument,
    ArgumentList,
    ParameterValueAssignment,

    // patterns
    VariablePattern,
    WildcardPattern,
    ExpressionPattern,
    TaggedPattern,
    OrderedStructurePatternMember,
    NamedStructurePatternMember,
    StructurePattern,
    MatchesClause,
    ConditionalPattern,
    ConditionalPredicate,

    // unary expressions
    UnaryPlusExpression,
    UnaryMinusExpression,
    UnaryBitwiseAndExpression,
    UnaryBitwiseNandExpression,
    UnaryBitwiseOrExpression,
    UnaryBitwiseNorExpression,
    UnaryBitwiseXorExpression,
    UnaryBitwiseXnorExpression,
    UnaryPreincrementExpression,
    UnaryPredecrementExpression,
    UnaryLogicalNotExpression,
    UnaryBitwiseNotExpression,

    // primary expressions
    NullLiteralExpression,
    StringLiteralExpression,
    IntegerLiteralExpression,
    IntegerVectorExpression,
    UnbasedUnsizedLiteralExpression,
    RealLiteralExpression,
    TimeLiteralExpression,
    WildcardLiteralExpression,
    OneStepLiteralExpression,
    ParenthesizedExpression,
    MinTypMaxExpression,
    EmptyQueueExpression,
    ConcatenationExpression,
    MultipleConcatenationExpression,
    StreamingConcatenationExpression,
    StreamExpression,
    StreamExpressionWithRange,
    NewClassExpression,
    NewArrayExpression,

    // selectors
    BitSelect,
    SimpleRangeSelect,
    AscendingRangeSelect,
    DescendingRangeSelect,
    ElementSelect,

    // postfix expressions
    ElementSelectExpression,
    MemberAccessExpression,
    InvocationExpression,
    PostincrementExpression,
    PostdecrementExpression,

    // binary expressions
    AddExpression,
    SubtractExpression,
    MultiplyExpression,
    DivideExpression,
    PowerExpression,
    ModExpression,
    EqualityExpression,
    InequalityExpression,
    CaseEqualityExpression,
    CaseInequalityExpression,
    WildcardEqualityExpression,
    WildcardInequalityExpression,
    LessThanExpression,
    LessThanEqualExpression,
    GreaterThanExpression,
    GreaterThanEqualExpression,
    LogicalAndExpression,
    LogicalOrExpression,
    BinaryAndExpression,
    BinaryOrExpression,
    BinaryXorExpression,
    BinaryXnorExpression,
    LogicalImplicationExpression,
    LogicalEquivalenceExpression,
    LogicalShiftLeftExpression,
    LogicalShiftRightExpression,
    ArithmeticShiftLeftExpression,
    ArithmeticShiftRightExpression,
    TaggedUnionExpression,
    InsideExpression,
    ConditionalExpression,

    // assignment expressions
    AssignmentExpression,
    AddAssignmentExpression,
    SubtractAssignmentExpression,
    MultiplyAssignmentExpression,
    DivideAssignmentExpression,
    ModAssignmentExpression,
    AndAssignmentExpression,
    OrAssignmentExpression,
    XorAssignmentExpression,
    LogicalLeftShiftAssignmentExpression,
    LogicalRightShiftAssignmentExpression,
    ArithmeticLeftShiftAssignmentExpression,
    ArithmeticRightShiftAssignmentExpression,

    // names
    LocalScope,
    UnitScope,
    RootScope,
    IdentifierName,
    IdentifierSelectName,
    ClassName,
    ScopedName,
    SystemName,
    ThisHandle,
    SuperHandle,
    ArrayUniqueMethod,
    ArrayAndMethod,
    ArrayOrMethod,
    ArrayXorMethod,
    ClassScope,

    // timing control
    DelayControl,
    CycleDelay,
    EventControl,
    IffClause,
    SignalEventExpression,
    BinaryEventExpression,
    ParenthesizedEventExpression,
    ImplicitEventControl,
    ParenImplicitEventControl,
    EventControlWithExpression,
    RepeatedEventControl,

    // declarations
    RangeDimensionSpecifier,
    DataTypeDimensionSpecifier,
    WildcardDimensionSpecifier,
    ColonExpressionClause,
    QueueDimensionSpecifier,
    VariableDimension,
    EqualsValueClause,
    VariableDeclarator,
    DataDeclaration,
    PackageImportItem,
    PackageImportDeclaration,
    ParameterDeclaration,
    TypeParameterDeclaration,
    ParameterDeclarationStatement,
    ChargeStrength,
    DriveStrength,
    NetDeclaration,
    PortDeclaration,
    GenvarDeclaration,

    // types
    BitType,
    LogicType,
    RegType,
    ByteType,
    ShortIntType,
    IntType,
    LongIntType,
    IntegerType,
    TimeType,
    ShortRealType,
    RealType,
    RealTimeType,
    StructType,
    UnionType,
    EnumType,
    StringType,
    CHandleType,
    VirtualInterfaceType,
    NamedType,
    EventType,
    VoidType,
    ImplicitType,
    TypeReference,
    StructUnionMember,
    DotMemberClause,

    // statements
    StatementLabel,
    EmptyStatement,
    ElseClause,
    ConditionalStatement,
    DefaultCaseItem,
    PatternCaseItem,
    StandardCaseItem,
    CaseStatement,
    ForeverStatement,
    LoopStatement,
    DoWhileStatement,
    ForVariableDeclaration,
    ForVariableAssignment,
    ForLoopStatement,
    ReturnStatement,
    JumpStatement,
    TimingControlStatement,
    ProceduralAssignStatement,
    ProceduralForceStatement,
    ProceduralDeassignStatement,
    ProceduralReleaseStatement,
    DisableStatement,
    DisableForkStatement,
    NamedBlockClause,
    SequentialBlockStatement,

    // assertions
    DeferredAssertion,
    ActionBlock,
    ImmediateAssertStatement,
    ImmediateAssumeStatement,
    ImmediateCoverStatement,

    // assignment statements
    NonblockingAssignmentStatement,
    BlockingAssignmentStatement,
    AddAssignmentStatement,
    SubtractAssignmentStatement,
    MultiplyAssignmentStatement,
    DivideAssignmentStatement,
    ModAssignmentStatement,
    AndAssignmentStatement,
    OrAssignmentStatement,
    XorAssignmentStatement,
    LogicalLeftShiftAssignmentStatement,
    LogicalRightShiftAssignmentStatement,
    ArithmeticLeftShiftAssignmentStatement,
    ArithmeticRightShiftAssignmentStatement,

    // modules
    ImplicitNonAnsiPort,
    ExplicitNonAnsiPort,
    NonAnsiPortList,
    InterfacePortHeader,
    VariablePortHeader,
    SimpleNetPortType,
    InterconnectPortHeader,
    DataNetPortType,
    NetPortHeader,
    ImplicitAnsiPort,
    ExplicitAnsiPort,
    AnsiPortList,
    WildcardPortList,
    ParameterPortList,
    ModuleHeader,
    ModuleDeclaration,
    InterfaceHeader,
    InterfaceDeclaration,
    ProgramHeader,
    ProgramDeclaration,
    ExternModule,

    // members
    EmptyMember,
    InitialBlock,
    FinalBlock,
    AlwaysBlock,
    AlwaysFFBlock,
    AlwaysCombBlock,
    AlwaysLatchBlock,
    GenerateRegion,
    LoopGenerate,
    DividerClause,
    TimeUnitsDeclaration,
    OrderedPortConnection,
    NamedPortConnection,
    WildcardPortConnection,
    HierarchicalInstance,
    HierarchyInstantiation,
    FunctionDeclaration,
    TaskDeclaration,

    // top level
    CompilationUnit
};

enum class TokenKind : uint16_t;

SyntaxKind getUnaryPrefixExpression(TokenKind kind);
SyntaxKind getUnaryPostfixExpression(TokenKind kind);
SyntaxKind getLiteralExpression(TokenKind kind);
SyntaxKind getBinaryExpression(TokenKind kind);
SyntaxKind getKeywordNameExpression(TokenKind kind);
SyntaxKind getAssignmentStatement(TokenKind kind);
SyntaxKind getIntegerType(TokenKind kind);
SyntaxKind getKeywordType(TokenKind kind);
SyntaxKind getProceduralBlockKind(TokenKind kind);
SyntaxKind getModuleDeclarationKind(TokenKind kind);
SyntaxKind getModuleHeaderKind(TokenKind kind);
TokenKind getModuleEndKind(TokenKind kind);
int getPrecedence(SyntaxKind kind);
bool isRightAssociative(SyntaxKind kind);
bool isPossibleDataType(TokenKind kind);
bool isPossibleExpression(TokenKind kind);
bool isPossibleStatement(TokenKind kind);
bool isNetType(TokenKind kind);
bool isPortDirection(TokenKind kind);
bool isPossibleArgument(TokenKind kind);
bool isComma(TokenKind kind);
bool isSemicolon(TokenKind kind);
bool isCloseBrace(TokenKind kind);
bool isIdentifierOrComma(TokenKind kind);
bool isPossibleExpressionOrComma(TokenKind kind);
bool isPossibleExpressionOrTripleAnd(TokenKind kind);
bool isPossibleInsideElement(TokenKind kind);
bool isPossiblePattern(TokenKind kind);
bool isPossibleDelayOrEventControl(TokenKind kind);
bool isEndKeyword(TokenKind kind);
bool isDeclarationModifier(TokenKind kind);
bool isEndOfParenList(TokenKind kind);
bool isEndOfBracedList(TokenKind kind);
bool isEndOfCaseItem(TokenKind kind);
bool isEndOfConditionalPredicate(TokenKind kind);
bool isEndOfAttribute(TokenKind kind);
bool isEndOfParameterList(TokenKind kind);
bool isNotInType(TokenKind kind);
bool isNotInPortReference(TokenKind kind);
bool isPossibleAnsiPort(TokenKind kind);
bool isPossibleNonAnsiPort(TokenKind kind);
bool isPossibleParameter(TokenKind kind);
bool isPossiblePortConnection(TokenKind kind);
bool isPossibleVectorDigit(TokenKind kind);

// discriminated union of Token and SyntaxNode
struct TokenOrSyntax {
    union {
        Token* token;
        SyntaxNode* node;
    };
    bool isToken;

    TokenOrSyntax(Token* token) : token(token), isToken(true) {}
    TokenOrSyntax(SyntaxNode* node) : node(node), isToken(false) {}
    TokenOrSyntax(std::nullptr_t) : token(nullptr), isToken(true) {}
};

// base class for all syntax nodes
class SyntaxNode {
public:
    uint32_t childCount = 0;
    SyntaxKind kind;

    SyntaxNode(SyntaxKind kind) : kind(kind) {}

    std::string toString(uint8_t flags = 0);

    void writeTo(Buffer<char>& buffer, uint8_t flags);
    Token* getFirstToken();

    template<typename T>
    T* as() {
        // TODO: assert kind
        return static_cast<T*>(this);
    }

    virtual TokenOrSyntax getChild(uint32_t);
};

template<typename T>
class SyntaxList : public SyntaxNode {
public:
    SyntaxList(std::nullptr_t) : SyntaxList(ArrayRef<T*>(nullptr)) {}
    SyntaxList(ArrayRef<T*> elements) :
        SyntaxNode(SyntaxKind::List),
        elements(elements)
    {
        childCount = elements.count();
    }

    uint32_t count() const { return elements.count(); }

    T* const* begin() const { return elements.begin(); }
    T* const* end() const { return elements.end(); }

    const T* operator[](uint32_t index) const { return elements[index]; }

protected:
    TokenOrSyntax getChild(uint32_t index) override final { return elements[index]; }

private:
    ArrayRef<T*> elements;
};

class TokenList : public SyntaxNode {
public:
    TokenList(std::nullptr_t) : TokenList(ArrayRef<Token*>(nullptr)) {}
    TokenList(ArrayRef<Token*> elements) :
        SyntaxNode(SyntaxKind::List),
        elements(elements)
    {
        childCount = elements.count();
    }

    uint32_t count() const { return elements.count(); }

    Token* const* begin() const { return elements.begin(); }
    Token* const* end() const { return elements.end(); }

    const Token* operator[](uint32_t index) const { return elements[index]; }

protected:
    TokenOrSyntax getChild(uint32_t index) override final { return elements[index]; }

private:
    ArrayRef<Token*> elements;
};

template<typename T>
class SeparatedSyntaxList : public SyntaxNode {
public:
    SeparatedSyntaxList(std::nullptr_t) : SeparatedSyntaxList(ArrayRef<TokenOrSyntax>(nullptr)) {}
    SeparatedSyntaxList(ArrayRef<TokenOrSyntax> elements) :
        SyntaxNode(SyntaxKind::List),
        elements(elements)
    {
        childCount = elements.count();
    }

    uint32_t count() const { return (uint32_t)std::ceil(elements.count() / 2.0); }

    const T* operator[](uint32_t index) const {
        index <<= 1;
        ASSERT(!elements[index].isToken);
        return static_cast<const T*>(elements[index].node);
    }

protected:
    TokenOrSyntax getChild(uint32_t index) override final { return elements[index]; }

private:
    ArrayRef<TokenOrSyntax> elements;
};

}
