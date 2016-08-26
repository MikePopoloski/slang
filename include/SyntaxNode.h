#pragma once

#include <cmath>
#include <cstdint>
#include <cstddef>
#include <string>

#include "ArrayRef.h"
#include "Buffer.h"
#include "Token.h"

namespace slang {

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
    ElsIfDirective,
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
    SimpleAssignmentPattern,
    AssignmentPatternItem,
    StructuredAssignmentPattern,
    ReplicatedAssignmentPattern,

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
    AssignmentPatternExpression,
    DefaultPatternKeyExpression,

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
    CastExpression,
    ArrayMethodWithClause,
    IdentifierList,
    RandomizeMethodWithClause,

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
    OpenRangeList,
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
    NonblockingAssignmentExpression,

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
    ConstructorName,

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
    TimingControlExpression,

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
    TypedefDeclaration,
    TypedefModportDeclaration,
    TypedefKeywordDeclaration,
    TypedefInterfaceClassDeclaration,
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
    NamedLabel,
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
    ForLoopStatement,
    ForeachLoopList,
    ForeachLoopStatement,
    ReturnStatement,
    JumpStatement,
    TimingControlStatement,
    ExpressionStatement,
    ProceduralAssignStatement,
    ProceduralForceStatement,
    ProceduralDeassignStatement,
    ProceduralReleaseStatement,
    DisableStatement,
    DisableForkStatement,
    NamedBlockClause,
    SequentialBlockStatement,
    ParallelBlockStatement,
    WaitStatement,
    WaitForkStatement,
    WaitOrderStatement,
    RandCaseItem,
    RandCaseStatement,

    // assertions
    DeferredAssertion,
    ActionBlock,
    ImmediateAssertStatement,
    ImmediateAssumeStatement,
    ImmediateCoverStatement,

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
    PackageHeader,
    PackageDeclaration,
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
    IfGenerate,
    CaseGenerate,
    GenerateBlock,
    DividerClause,
    TimeUnitsDeclaration,
    OrderedPortConnection,
    NamedPortConnection,
    WildcardPortConnection,
    HierarchicalInstance,
    HierarchyInstantiation,
    FunctionPrototype,
    FunctionDeclaration,
    TaskDeclaration,
    ExtendsClause,
    ImplementsClause,
    ClassDeclaration,
    ClassPropertyDeclaration,
    ClassMethodDeclaration,
    ClassMethodPrototype,
    ContinuousAssign,
    DefParamAssignment,
    DefParam,

    // constraints
    DistWeight,
    DistItem,
    DistConstraintList,
    ExpressionConstraint,
    UniquenessConstraint,
    ImplicationConstraint,
    ElseConstraintClause,
    ConditionalConstraint,
    LoopConstraint,
    DisableConstraint,
    ConstraintBlock,
    ConstraintPrototype,
    ConstraintDeclaration,

    // covergroups
    WithFunctionSample,
    BinaryBlockEventExpression,
    PrimaryBlockEventExpression,
    BlockCoverageEvent,
    CovergroupDeclaration,
    CoverageOption,

    // top level
    CompilationUnit
};

enum class TokenKind : uint16_t;

SyntaxKind getUnaryPrefixExpression(TokenKind kind);
SyntaxKind getUnaryPostfixExpression(TokenKind kind);
SyntaxKind getLiteralExpression(TokenKind kind);
SyntaxKind getBinaryExpression(TokenKind kind);
SyntaxKind getKeywordNameExpression(TokenKind kind);
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
bool isPossibleExpressionOrCommaOrDefault(TokenKind kind);
bool isPossibleExpressionOrTripleAnd(TokenKind kind);
bool isPossibleOpenRangeElement(TokenKind kind);
bool isPossiblePattern(TokenKind kind);
bool isPossibleDelayOrEventControl(TokenKind kind);
bool isEndKeyword(TokenKind kind);
bool isDeclarationModifier(TokenKind kind);
bool isMemberQualifier(TokenKind kind);
bool isEndOfParenList(TokenKind kind);
bool isEndOfBracedList(TokenKind kind);
bool isEndOfCaseItem(TokenKind kind);
bool isEndOfConditionalPredicate(TokenKind kind);
bool isEndOfAttribute(TokenKind kind);
bool isEndOfParameterList(TokenKind kind);
bool isNotInType(TokenKind kind);
bool isNotInPortReference(TokenKind kind);
bool isNotInConcatenationExpr(TokenKind kind);
bool isPossibleAnsiPort(TokenKind kind);
bool isPossibleNonAnsiPort(TokenKind kind);
bool isPossibleParameter(TokenKind kind);
bool isPossiblePortConnection(TokenKind kind);
bool isPossibleVectorDigit(TokenKind kind);

// discriminated union of Token and SyntaxNode
struct TokenOrSyntax {
    union {
        Token token;
        SyntaxNode* node;
    };
    bool isToken;

    TokenOrSyntax(Token token) : token(token), isToken(true) {}
    TokenOrSyntax(SyntaxNode* node) : node(node), isToken(false) {}
    TokenOrSyntax(std::nullptr_t) : token(), isToken(true) {}
};

// base class for all syntax nodes
class SyntaxNode {
public:
    uint32_t childCount = 0;
    SyntaxKind kind;

    SyntaxNode(SyntaxKind kind) : kind(kind) {}

    std::string toString(uint8_t flags = 0);

    void writeTo(Buffer<char>& buffer, uint8_t flags);
    Token getFirstToken();
    bool replaceFirstToken(Token token);

    template<typename T>
    T* as() {
        // TODO: assert kind
        return static_cast<T*>(this);
    }

protected:
    virtual TokenOrSyntax getChild(uint32_t) = 0;
    virtual void replaceChild(uint32_t, Token) = 0;
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
    T* operator[](uint32_t index) { return elements[index]; }

protected:
    TokenOrSyntax getChild(uint32_t index) override final { return elements[index]; }
    virtual void replaceChild(uint32_t, Token) override final { ASSERT(false, "No tokens in SyntaxList!"); };

private:
    ArrayRef<T*> elements;
};

class TokenList : public SyntaxNode {
public:
    TokenList(std::nullptr_t) : TokenList(ArrayRef<Token>(nullptr)) {}
    TokenList(ArrayRef<Token> elements) :
        SyntaxNode(SyntaxKind::List),
        elements(elements)
    {
        childCount = elements.count();
    }

    uint32_t count() const { return elements.count(); }

    const Token* begin() const { return elements.begin(); }
    const Token* end() const { return elements.end(); }

    const Token operator[](uint32_t index) const { return elements[index]; }
    Token operator[](uint32_t index) { return elements[index]; }

protected:
    TokenOrSyntax getChild(uint32_t index) override final { return elements[index]; }
    virtual void replaceChild(uint32_t index, Token child) override final { elements[index] = child; };

private:
    ArrayRef<Token> elements;
};

template<typename T>
class SeparatedSyntaxList : public SyntaxNode {
public:
    class iterator : public std::iterator<std::forward_iterator_tag, T*> {
    public:
        iterator(SeparatedSyntaxList& list);

        iterator& operator++();
        reference operator*() const;
        pointer operator->() const;

        bool operator==(const iterator& a) const;
        bool operator!=(const iterator& b) const;
    };

    SeparatedSyntaxList(std::nullptr_t) : SeparatedSyntaxList(ArrayRef<TokenOrSyntax>(nullptr)) {}
    SeparatedSyntaxList(ArrayRef<TokenOrSyntax> elements) :
        SyntaxNode(SyntaxKind::List),
        elements(elements)
    {
        childCount = elements.count();
    }

    bool empty() const { return count() == 0; }
    uint32_t count() const { return (uint32_t)std::ceil(elements.count() / 2.0); }

    const T* operator[](uint32_t index) const {
        return const_cast<SeparatedSyntaxList*>(this)->operator[](index);
    }

    T* operator[](uint32_t index) {
        index <<= 1;
        ASSERT(!elements[index].isToken);
        return static_cast<T*>(elements[index].node);
    }

    iterator begin();
    iterator end();

protected:
    TokenOrSyntax getChild(uint32_t index) override final { return elements[index]; }
    virtual void replaceChild(uint32_t index, Token child) override final {
        ASSERT(elements[index].isToken);
        elements[index].token = child;
    };

private:
    ArrayRef<TokenOrSyntax> elements;
};

}
