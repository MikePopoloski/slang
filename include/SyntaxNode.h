//------------------------------------------------------------------------------
// SyntaxNode.h
// Base class and utilities for syntax nodes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <cmath>
#include <cstdint>
#include <cstddef>
#include <string>

#include "ArrayRef.h"
#include "SmallVector.h"
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

    // misc expressions
    TaggedUnionExpression,
    OpenRangeList,
    InsideExpression,
    ConditionalExpression,
    ExpressionOrDist,
    BadExpression,

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
    UnarySequenceDelayExpression,
    UnarySequenceEventExpression,
    UnaryNotPropertyExpression,
    AcceptOnPropertyExpression,
    RejectOnPropertyExpression,
    SyncAcceptOnPropertyExpression,
    SyncRejectOnPropertyExpression,
    NextTimePropertyExpression,
    SNextTimePropertyExpression,
    AlwaysPropertyExpression,
    SAlwaysPropertyExpression,
    EventuallyPropertyExpression,
    SEventuallyPropertyExpression,

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
    NewExpression,

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
    SignedCastExpression,
    WithClause,
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
    BinarySequenceDelayExpression,
    OrSequenceExpression,
    AndSequenceExpression,
    IntersectSequenceExpression,
    WithinSequenceExpression,
    ThroughoutSequenceExpression,
    IffPropertyExpression,
    UntilPropertyExpression,
    SUntilPropertyExpression,
    UntilWithPropertyExpression,
    SUntilWithPropertyExpression,
    ImpliesPropertyExpression,
    OverlappedImplicationPropertyExpression,
    NonOverlappedImplicationPropertyExpression,
    OverlappedFollowedByPropertyExpression,
    NonOverlappedFollowedByPropertyExpression,

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
    EmptyIdentifierName,
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
    SignalEventExpression,
    BinaryEventExpression,
    ParenthesizedEventExpression,
    ImplicitEventControl,
    ParenImplicitEventControl,
    EventControlWithExpression,
    RepeatedEventControl,
    TimingControlExpression,
    ShortcutCycleDelayRange,

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
    TypedefKeywordDeclaration,
    TypedefInterfaceClassDeclaration,
    PackageImportItem,
    PackageImportDeclaration,
    ParameterDeclaration,
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
    TypeType,
    ImplicitType,
    TypeReference,
    StructUnionMember,
    DotMemberClause,
    Untyped,
    PropertyType,
    SequenceType,
    VarDataType,

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
    BlockingEventTriggerStatement,
    NonblockingEventTriggerStatement,

    // assertions
    DeferredAssertion,
    ConcurrentAssertionMember,
    ImmediateAssertionMember,
    ActionBlock,
    ImmediateAssertStatement,
    ImmediateAssumeStatement,
    ImmediateCoverStatement,
    DisableIff,
    PropertySpec,
    AssertPropertyStatement,
    AssumePropertyStatement,
    CoverPropertyStatement,
    CoverSequenceStatement,
    RestrictPropertyStatement,
    ExpectPropertyStatement,

    // modules
    ImplicitNonAnsiPort,
    ExplicitNonAnsiPort,
    NonAnsiPortList,
    InterfacePortHeader,
    VariablePortHeader,
    InterconnectPortHeader,
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
    FunctionPort,
    FunctionPortList,
    FunctionPrototype,
    FunctionDeclaration,
    LetPort,
    LetPortList,
    LetDeclaration,
    AssertionVariableDeclaration,
    PropertyLvarPortDirection,
    PropertyLocalPort,
    PropertyPort,
    PropertyPortList,
    PropertyDeclaration,
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
    ModportItem,
    ModportDeclaration,

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
    Coverpoint,
    DefaultCoverageBinInitializer,
    ExpressionCoverageBinInitializer,
    RangeCoverageBinInitializer,
    IffClause,
    CoverageBins,

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
bool isEndOfBracketedList(TokenKind kind);
bool isEndOfCaseItem(TokenKind kind);
bool isEndOfConditionalPredicate(TokenKind kind);
bool isEndOfAttribute(TokenKind kind);
bool isEndOfParameterList(TokenKind kind);
bool isNotInType(TokenKind kind);
bool isNotInPortReference(TokenKind kind);
bool isNotInConcatenationExpr(TokenKind kind);
bool isNotInParameterList(TokenKind kind);
bool isPossiblePropertyPortItem(TokenKind kind);
bool isPossibleAnsiPort(TokenKind kind);
bool isPossibleNonAnsiPort(TokenKind kind);
bool isPossibleFunctionPort(TokenKind kind);
bool isPossibleParameter(TokenKind kind);
bool isPossiblePortConnection(TokenKind kind);
bool isPossibleVectorDigit(TokenKind kind);
bool isPossibleLetPortItem(TokenKind kind);
bool isStatement(SyntaxKind kind);
bool isExpression(SyntaxKind kind);

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

/// Base class for all syntax nodes.
class SyntaxNode {
public:
    /// The kind of syntax node.
    SyntaxKind kind;

    SyntaxNode(SyntaxKind kind) : kind(kind) {}

    /// Utility method to wrap writeTo and generate an std::string.
    std::string toString(uint8_t flags = 0);
    std::string toString(uint8_t flags = 0) const;

    /// Write the node and all of its children to a string.
    void writeTo(SmallVector<char>& buffer, uint8_t flags);

    /// Get the first leaf token in this subtree.
    Token getFirstToken();
    Token getFirstToken() const;

    /// Get the last leaf token in this subtree.
    Token getLastToken();
    Token getLastToken() const;

    /// Get the source range of the node.
    SourceRange sourceRange() const;

    /// Replace the first token in the subtree with the given token.
    bool replaceFirstToken(Token token);

    /// Gets the child syntax node at the specified index. If the child at
    /// the given index is not a node (probably a token) then this returns null.
    const SyntaxNode* childNode(uint32_t index) const;
    uint32_t getChildCount() const { return childCount; }

    template<typename T>
    T* as() {
        // TODO: assert kind
        return static_cast<T*>(this);
    }

    template<typename T>
    const T* as() const {
        // TODO: assert kind
        return static_cast<const T*>(this);
    }

    // The following is some template magic to determine whether a type has a
    // visit() function taking a specific argument, and if so call it. Otherwise
    // it calls visitDefault().
    template<typename, typename T>
    struct has_visit {
        static_assert(
            std::integral_constant<T, false>::value,
            "Second template parameter needs to be of function type.");
    };

    template<typename C, typename Ret, typename... Args>
    struct has_visit<C, Ret(Args...)> {
    private:
        template<typename T>
        static constexpr auto check(T*) -> typename
            std::is_same<
                decltype(std::declval<T>().visit(std::declval<Args>()...)),
                Ret
            >::type;

        template<typename>
        static constexpr std::false_type check(...);

        typedef decltype(check<C>(0)) type;

    public:
        static constexpr bool value = type::value;
    };

    template<typename C, typename... Args>
    static std::enable_if_t<has_visit<C, void(Args...)>::value> dispatch(C& c, Args&&... args) {
        c.visit(std::forward<Args>(args)...);
    }

    template<typename C, typename... Args>
    static std::enable_if_t<!has_visit<C, void(Args...)>::value> dispatch(C& c, Args&&... args) {
        c.visitDefault(std::forward<Args>(args)...);
    }

protected:
    uint32_t childCount = 0;

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

    const T* const* begin() const { return elements.begin(); }
    const T* const* end() const { return elements.end(); }

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
    template<typename TOwner, typename TValue>
    class iterator_templ {
    public:
        using difference_type = ptrdiff_t;
        using value_type = TValue*;
        using pointer = TValue**;
        using reference = TValue*;
        using iterator_category = std::forward_iterator_tag;

        iterator_templ(TOwner& list, int index) :
            list(list), index(index)
        {
        }

        iterator_templ& operator++() { ++index; return *this; }
        iterator_templ operator++(int) {
            iterator_templ result = *this;
            ++(*this);
            return result;
        }

        reference operator*() const { return list[index]; }
        pointer operator->() const { return &list[index]; }

        bool operator==(const iterator_templ& other) const { return &list == &other.list && index == other.index; }
        bool operator!=(const iterator_templ& other) const { return !(*this == other); }

    private:
        TOwner& list;
        int index;
    };

    using iterator = iterator_templ<SeparatedSyntaxList, T>;
    using const_iterator = iterator_templ<const SeparatedSyntaxList, const T>;

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

    iterator begin() { return iterator(*this, 0); }
    iterator end() { return iterator(*this, count()); }

    const_iterator begin() const { return cbegin(); }
    const_iterator end() const { return cend(); }
    const_iterator cbegin() const { return const_iterator(*this, 0); }
    const_iterator cend() const { return const_iterator(*this, count()); }

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
