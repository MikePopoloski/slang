#pragma once

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
    LogicalNotExpression,
    BitwiseNotExpression,

    // primary expressions
    NullLiteralExpression,
    StringLiteralExpression,
    IntegerLiteralExpression,
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
    ExpressionDimensionSpecifier,
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
    ParameterAssignment,

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
    InitialBlock,
    FinalBlock,
    AlwaysBlock,
    AlwaysFFBlock,
    AlwaysCombBlock,
    AlwaysLatchBlock,
    GenerateBlock,
    DividerClause,
    TimeUnitsDeclaration,
    OrderedPortConnection,
    NamedPortConnection,
    WildcardPortConnection,
    HierarchicalInstance,
    HierarchyInstantiation
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

std::ostream& operator<<(std::ostream& os, SyntaxKind kind);

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

    // convenience methods that wrap writeTo
    // toFullString() includes trivia, toString() does not
    std::string toString();
    std::string toFullString();

    void writeTo(Buffer<char>& buffer, bool includeTrivia, bool includeMissing = false);
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