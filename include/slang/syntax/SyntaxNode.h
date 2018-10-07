//------------------------------------------------------------------------------
// SyntaxNode.h
// Base class and utilities for syntax nodes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <string>

#include "slang/parsing/Token.h"
#include "slang/util/Iterator.h"
#include "slang/util/SmallVector.h"

namespace slang {

class SyntaxNode;

enum class SyntaxKind : uint16_t;
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
bool isEndOfTransSet(TokenKind kind);
bool isNotInType(TokenKind kind);
bool isNotInPortReference(TokenKind kind);
bool isNotInConcatenationExpr(TokenKind kind);
bool isNotInParameterList(TokenKind kind);
bool isPossiblePropertyPortItem(TokenKind kind);
bool isPossibleAnsiPort(TokenKind kind);
bool isPossibleNonAnsiPort(TokenKind kind);
bool isPossibleModportPort(TokenKind kind);
bool isPossibleFunctionPort(TokenKind kind);
bool isPossibleParameter(TokenKind kind);
bool isPossiblePortConnection(TokenKind kind);
bool isPossibleVectorDigit(TokenKind kind);
bool isPossibleLetPortItem(TokenKind kind);
bool isPossibleTransSet(TokenKind kind);
bool isBeforeOrSemicolon(TokenKind kind);
bool isStatement(SyntaxKind kind);
bool isExpression(SyntaxKind kind);

template<typename TNode>
struct TokenOrSyntaxBase : public std::variant<Token, TNode> {
    using Base = std::variant<Token, TNode>;
    TokenOrSyntaxBase(Token token) : Base(token) {}
    TokenOrSyntaxBase(TNode node) : Base(node) {}
    TokenOrSyntaxBase(nullptr_t) : Base(Token()) {}

    bool isToken() const { return this->index() == 0; }
    bool isNode() const { return this->index() == 1; }

    Token token() const { return std::get<0>(*this); }
    TNode node() const { return std::get<1>(*this); }

protected:
    TokenOrSyntaxBase() = default;
};

struct TokenOrSyntax : public TokenOrSyntaxBase<SyntaxNode*> {
    using TokenOrSyntaxBase::TokenOrSyntaxBase;
};

struct ConstTokenOrSyntax : public TokenOrSyntaxBase<const SyntaxNode*> {
    using TokenOrSyntaxBase::TokenOrSyntaxBase;

    ConstTokenOrSyntax(TokenOrSyntax tos);
};

/// Base class for all syntax nodes.
class SyntaxNode {
public:
    /// The parent node of this syntax node. The root of the syntax
    /// tree does not have a parent (will be nullptr).
    SyntaxNode* parent = nullptr;

    /// The kind of syntax node.
    SyntaxKind kind;

    /// Print the node and all of its children to a string.
    std::string toString() const;

    /// Get the first leaf token in this subtree.
    Token getFirstToken() const;

    /// Get the last leaf token in this subtree.
    Token getLastToken() const;

    /// Get the source range of the node.
    SourceRange sourceRange() const;

    /// Gets the child syntax node at the specified index. If the child at
    /// the given index is not a node (probably a token) then this returns null.
    const SyntaxNode* childNode(uint32_t index) const;
    Token childToken(uint32_t index) const;

    uint32_t getChildCount() const; // Note: implemented in AllSyntax.cpp

    template<typename T>
    T& as() {
        ASSERT(T::isKind(kind));
        return *static_cast<T*>(this);
    }

    template<typename T>
    const T& as() const {
        ASSERT(T::isKind(kind));
        return *static_cast<const T*>(this);
    }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args);

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor& visitor, Args&&... args) const;

    static bool isKind(SyntaxKind) { return true; }

protected:
    explicit SyntaxNode(SyntaxKind kind) : kind(kind) {}

private:
    ConstTokenOrSyntax getChild(uint32_t index) const;
};

class SyntaxListBase : public SyntaxNode {
public:
    uint32_t getChildCount() const { return childCount; }

    virtual TokenOrSyntax getChild(uint32_t index) = 0;
    virtual ConstTokenOrSyntax getChild(uint32_t index) const = 0;
    virtual void setChild(uint32_t index, TokenOrSyntax child) = 0;

    virtual SyntaxListBase* clone(BumpAllocator& alloc) const = 0;

    virtual void resetAll(BumpAllocator& alloc, span<const TokenOrSyntax> children) = 0;

    static bool isKind(SyntaxKind kind);

protected:
    SyntaxListBase(SyntaxKind kind, uint32_t childCount) :
        SyntaxNode(kind), childCount(childCount) {}

    uint32_t childCount;
};

template<typename T>
class SyntaxList : public SyntaxListBase, public span<T*> {
public:
    SyntaxList(nullptr_t) : SyntaxList(span<T*>()) {}
    SyntaxList(span<T*> elements);

private:
    TokenOrSyntax getChild(uint32_t index) override final { return (*this)[index]; }
    ConstTokenOrSyntax getChild(uint32_t index) const override final { return (*this)[index]; }

    void setChild(uint32_t index, TokenOrSyntax child) override final {
        (*this)[index] = &child.node()->as<T>();
    }

    SyntaxListBase* clone(BumpAllocator& alloc) const override final {
        return alloc.emplace<SyntaxList<T>>(*this);
    }

    void resetAll(BumpAllocator& alloc, span<const TokenOrSyntax> children) override final {
        SmallVectorSized<T*, 8> buffer((uint32_t)children.size());
        for (auto& t : children)
            buffer.append(&t.node()->as<T>());

        *this = buffer.copy(alloc);
        childCount = buffer.size();
    }
};

class TokenList : public SyntaxListBase, public span<Token> {
public:
    TokenList(nullptr_t) : TokenList(span<Token>()) {}
    TokenList(span<Token> elements);

private:
    TokenOrSyntax getChild(uint32_t index) override final { return (*this)[index]; }
    ConstTokenOrSyntax getChild(uint32_t index) const override final { return (*this)[index]; }
    void setChild(uint32_t index, TokenOrSyntax child) override final {
        (*this)[index] = child.token();
    }

    SyntaxListBase* clone(BumpAllocator& alloc) const override final {
        return alloc.emplace<TokenList>(*this);
    }

    void resetAll(BumpAllocator& alloc, span<const TokenOrSyntax> children) override final {
        SmallVectorSized<Token, 8> buffer((uint32_t)children.size());
        for (auto& t : children)
            buffer.append(t.token());

        *this = buffer.copy(alloc);
        childCount = buffer.size();
    }
};

template<typename T>
class SeparatedSyntaxList : public SyntaxListBase {
public:
    using size_type = span<TokenOrSyntax>::size_type;

    template<typename U>
    class iterator_base
        : public iterator_facade<iterator_base<U>, std::random_access_iterator_tag, U, size_type> {
    public:
        using ParentList = std::conditional_t<std::is_const_v<std::remove_pointer_t<U>>,
                                              const SeparatedSyntaxList, SeparatedSyntaxList>;
        iterator_base(ParentList& list, size_type index) : list(list), index(index) {}

        bool operator==(const iterator_base& other) const {
            return &list == &other.list && index == other.index;
        }

        bool operator<(const iterator_base& other) const { return index < other.index; }

        U operator*() const { return list[index]; }

        size_type operator-(const iterator_base& other) const { return index - other.index; }

        iterator_base& operator+=(int32_t n) {
            index += n;
            return *this;
        }
        iterator_base& operator-=(int32_t n) {
            index -= n;
            return *this;
        }

    private:
        ParentList& list;
        size_type index;
    };

    using iterator = iterator_base<T*>;
    using const_iterator = iterator_base<const T*>;

    SeparatedSyntaxList(nullptr_t) : SeparatedSyntaxList(span<TokenOrSyntax>()) {}
    SeparatedSyntaxList(span<TokenOrSyntax> elements);

    bool empty() const { return elements.empty(); }
    span<TokenOrSyntax>::size_type size() const { return (elements.size() + 1) / 2; }

    const T* operator[](size_type index) const {
        index <<= 1;
        return &elements[index].node()->template as<T>();
    }

    T* operator[](size_type index) {
        index <<= 1;
        return &elements[index].node()->template as<T>();
    }

    iterator begin() { return iterator(*this, 0); }
    iterator end() { return iterator(*this, size()); }
    const_iterator begin() const { return cbegin(); }
    const_iterator end() const { return cend(); }
    const_iterator cbegin() const { return const_iterator(*this, 0); }
    const_iterator cend() const { return const_iterator(*this, size()); }

private:
    TokenOrSyntax getChild(uint32_t index) override final { return elements[index]; }
    ConstTokenOrSyntax getChild(uint32_t index) const override final { return elements[index]; }
    void setChild(uint32_t index, TokenOrSyntax child) override final { elements[index] = child; }

    SyntaxListBase* clone(BumpAllocator& alloc) const override final {
        return alloc.emplace<SeparatedSyntaxList<T>>(*this);
    }

    void resetAll(BumpAllocator& alloc, span<const TokenOrSyntax> children) override final {
        SmallVectorSized<TokenOrSyntax, 8> buffer((uint32_t)children.size());
        buffer.appendRange(children);

        elements = buffer.copy(alloc);
        childCount = buffer.size();
    }

    span<TokenOrSyntax> elements;
};

enum class SyntaxKind : uint16_t {
    Unknown,
    SyntaxList,
    TokenList,
    SeparatedList,

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
    EmptyArgument,
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
    TimingControlExpressionConcatenation,
    ShortcutCycleDelayRange,

    // declarations
    RangeDimensionSpecifier,
    WildcardDimensionSpecifier,
    ColonExpressionClause,
    QueueDimensionSpecifier,
    VariableDimension,
    EqualsValueClause,
    VariableDeclarator,
    DataDeclaration,
    TypedefDeclaration,
    ForwardTypedefDeclaration,
    ForwardInterfaceClassTypedefDeclaration,
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
    PortReference,
    PortConcatenation,
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
    AssertionItemPort,
    AssertionItemPortList,
    LetDeclaration,
    PropertyDeclaration,
    SequenceDeclaration,
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
    ModportClockingPort,
    ModportNamedPort,
    ModportExplicitPort,
    ModportSimplePortList,
    ModportSubroutinePort,
    ModportSubroutinePortList,
    ModportItem,
    ModportDeclaration,
    ClockingSkew,
    ClockingDirection,
    ClockingItem,
    ClockingDeclaration,
    DPIImportExport,

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
    SolveBeforeConstraint,
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
    TransRepeatRange,
    TransRange,
    TransSet,
    DefaultCoverageBinInitializer,
    ExpressionCoverageBinInitializer,
    RangeCoverageBinInitializer,
    TransListCoverageBinInitializer,
    IffClause,
    CoverageBins,

    // top level
    CompilationUnit
};

template<typename T>
SyntaxList<T>::SyntaxList(span<T*> elements) :
    SyntaxListBase(SyntaxKind::SyntaxList, (uint32_t)elements.size()), span<T*>(elements) {
}

inline TokenList::TokenList(span<Token> elements) :
    SyntaxListBase(SyntaxKind::TokenList, (uint32_t)elements.size()), span<Token>(elements) {
}

template<typename T>
SeparatedSyntaxList<T>::SeparatedSyntaxList(span<TokenOrSyntax> elements) :
    SyntaxListBase(SyntaxKind::SeparatedList, (uint32_t)elements.size()), elements(elements) {
}

} // namespace slang
