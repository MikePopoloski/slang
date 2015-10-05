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
    ParenthesizedExpression,
    MinTypMaxExpression,
    EmptyQueueExpression,
    ConcatenationExpression,
    MultipleConcatenationExpression,
    StreamingConcatenationExpression,
    StreamExpression,
    StreamExpressionWithRange,

    // postfix expressions
    InvocationExpression,

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
    ClassOrPackageScope,
    RootScope,
    IdentifierName,
    HierarchicalName,
    SystemName,
    ThisHandle,
    SuperHandle,
};

enum class TokenKind : uint16_t;

SyntaxKind getUnaryExpression(TokenKind kind);
SyntaxKind getLiteralExpression(TokenKind kind);
SyntaxKind getBinaryExpression(TokenKind kind);
SyntaxKind getAssignmentExpression(TokenKind kind);
SyntaxKind getKeywordNameExpression(TokenKind kind);
int getPrecedence(SyntaxKind kind);
bool isRightAssociative(SyntaxKind kind);

// discriminated union of Token and SyntaxNode
struct TokenOrSyntax {
    union {
        const Token* token;
        const SyntaxNode* node;
    };
    bool isToken;

    TokenOrSyntax(const Token* token) : token(token), isToken(true) {}
    TokenOrSyntax(const SyntaxNode* node) : node(node), isToken(false) {}
    TokenOrSyntax(std::nullptr_t) : token(nullptr), isToken(true) {}
};

// base class for all syntax nodes
class SyntaxNode {
public:
    SyntaxKind kind;

    SyntaxNode(SyntaxKind kind) : kind(kind) {}

    // convenience methods that wrap writeTo
    // toFullString() includes trivia, toString() does not
    std::string toString() const;
    std::string toFullString() const;

    void writeTo(Buffer<char>& buffer, bool includeTrivia) const;

    template<typename T>
    T* as() {
        // TODO: assert kind
        return static_cast<T*>(this);
    }

    int getChildCount() const { return childCount; }

protected:
    uint32_t childCount = 0;
    virtual TokenOrSyntax getChild(uint32_t) const;
};

template<typename T>
class SyntaxList : public SyntaxNode {
public:
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
    TokenOrSyntax getChild(uint32_t index) const override final { return elements[index]; }

private:
    ArrayRef<T*> elements;
};

class TokenList : public SyntaxNode {
public:
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
    TokenOrSyntax getChild(uint32_t index) const override final { return elements[index]; }

private:
    ArrayRef<Token*> elements;
};

template<typename T>
class SeparatedSyntaxList : public SyntaxNode {
public:
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
    TokenOrSyntax getChild(uint32_t index) const override final { return elements[index]; }

private:
    ArrayRef<TokenOrSyntax> elements;
};

}