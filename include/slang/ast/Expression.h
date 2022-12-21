//------------------------------------------------------------------------------
//! @file Expression.h
//! @brief Expression creation and analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/ASTContext.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/LValue.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/util/StackContainer.h"

namespace slang::ast {

class ASTSerializer;
class InstanceSymbolBase;
class Type;
class ValueSymbol;

// clang-format off
#define EXPRESSION(x) \
    x(Invalid) \
    x(IntegerLiteral) \
    x(RealLiteral) \
    x(TimeLiteral) \
    x(UnbasedUnsizedIntegerLiteral) \
    x(NullLiteral) \
    x(UnboundedLiteral) \
    x(StringLiteral) \
    x(NamedValue) \
    x(HierarchicalValue) \
    x(UnaryOp) \
    x(BinaryOp) \
    x(ConditionalOp) \
    x(Inside) \
    x(Assignment) \
    x(Concatenation) \
    x(Replication) \
    x(Streaming) \
    x(ElementSelect) \
    x(RangeSelect) \
    x(MemberAccess) \
    x(Call) \
    x(Conversion) \
    x(DataType) \
    x(TypeReference) \
    x(ArbitrarySymbol) \
    x(LValueReference) \
    x(SimpleAssignmentPattern) \
    x(StructuredAssignmentPattern) \
    x(ReplicatedAssignmentPattern) \
    x(EmptyArgument) \
    x(OpenRange) \
    x(Dist) \
    x(NewArray) \
    x(NewClass) \
    x(NewCovergroup) \
    x(CopyClass) \
    x(MinTypMax) \
    x(ClockingEvent) \
    x(AssertionInstance) \
    x(TaggedUnion)
ENUM(ExpressionKind, EXPRESSION)
#undef EXPRESSION

#define OP(x) \
    x(Plus) \
    x(Minus) \
    x(BitwiseNot) \
    x(BitwiseAnd) \
    x(BitwiseOr) \
    x(BitwiseXor) \
    x(BitwiseNand) \
    x(BitwiseNor) \
    x(BitwiseXnor) \
    x(LogicalNot) \
    x(Preincrement) \
    x(Predecrement) \
    x(Postincrement) \
    x(Postdecrement)
ENUM(UnaryOperator, OP)
#undef OP

#define OP(x) \
    x(Add) \
    x(Subtract) \
    x(Multiply) \
    x(Divide) \
    x(Mod) \
    x(BinaryAnd) \
    x(BinaryOr) \
    x(BinaryXor) \
    x(BinaryXnor) \
    x(Equality) \
    x(Inequality) \
    x(CaseEquality) \
    x(CaseInequality) \
    x(GreaterThanEqual) \
    x(GreaterThan) \
    x(LessThanEqual) \
    x(LessThan) \
    x(WildcardEquality) \
    x(WildcardInequality) \
    x(LogicalAnd) \
    x(LogicalOr) \
    x(LogicalImplication) \
    x(LogicalEquivalence) \
    x(LogicalShiftLeft) \
    x(LogicalShiftRight) \
    x(ArithmeticShiftLeft) \
    x(ArithmeticShiftRight) \
    x(Power)
ENUM(BinaryOperator, OP)
#undef OP

#define RANGE(x) x(Simple) x(IndexedUp) x(IndexedDown)
ENUM(RangeSelectionKind, RANGE)
#undef RANGE
// clang-format on

/// The base class for all expressions in SystemVerilog.
class SLANG_EXPORT Expression {
public:
    using ExpressionSyntax = syntax::ExpressionSyntax;

    /// The kind of expression; indicates the type of derived class.
    ExpressionKind kind;

    /// The type of the expression.
    not_null<const Type*> type;

    /// A pointer to a constant value if the expression has been evaluated.
    /// The value may be empty to indicate that the expression is known to not be constant.
    /// If the pointer is null, the expression hasn't been evaluated yet.
    mutable const ConstantValue* constant = nullptr;

    /// The syntax used to create the expression, if any. An expression tree can
    /// be created manually in which case it may not have a syntax representation.
    const ExpressionSyntax* syntax = nullptr;

    /// The source range of this expression, if it originated from source code.
    SourceRange sourceRange;

    Expression(const Expression&) = delete;
    Expression& operator=(const Expression&) = delete;

    /// Binds an expression tree from the given syntax nodes.
    static const Expression& bind(const ExpressionSyntax& syntax, const ASTContext& context,
                                  bitmask<ASTFlags> extraFlags = ASTFlags::None);

    /// Binds the left hand side of an assignment-like expression from the given syntax nodes.
    static const Expression& bindLValue(const ExpressionSyntax& lhs, const Type& rhs,
                                        SourceLocation location, const ASTContext& context,
                                        bool isInout);

    /// Binds an lvalue that is not a typical assignment-like context. For example, the
    /// output argument of certain system tasks that accept almost any type.
    static const Expression& bindLValue(const ExpressionSyntax& syntax, const ASTContext& context);

    /// Binds the right hand side of an assignment-like expression from the given syntax nodes.
    static const Expression& bindRValue(const Type& lhs, const ExpressionSyntax& rhs,
                                        SourceLocation location, const ASTContext& context,
                                        bitmask<ASTFlags> extraFlags = ASTFlags::None);

    /// Binds a connection to a ref argument from the given syntax nodes.
    static const Expression& bindRefArg(const Type& lhs, bool isConstRef,
                                        const ExpressionSyntax& rhs, SourceLocation location,
                                        const ASTContext& context);

    /// Binds an argument or port connection with the given direction and syntax nodes.
    static const Expression& bindArgument(const Type& argType, ArgumentDirection direction,
                                          const ExpressionSyntax& syntax, const ASTContext& context,
                                          bool isConstRef = false);

    /// Binds an initializer expression for an implicitly typed parameter.
    /// There are special inference rules for parameters.
    static std::tuple<const Expression*, const Type*> bindImplicitParam(
        const syntax::DataTypeSyntax& implicitType, const ExpressionSyntax& rhs,
        SourceLocation location, const ASTContext& exprContext, const ASTContext& typeContext,
        bitmask<ASTFlags> extraFlags = ASTFlags::None);

    /// Bind a selector expression given an already existing value to select from.
    static const Expression& bindSelector(Expression& value,
                                          const syntax::ElementSelectSyntax& syntax,
                                          const ASTContext& context);

    /// Tries to bind an interface reference into an expression for an interface port
    /// or a virtual interface assignment.
    /// Returns nullptr if unable to do so.
    static Expression* tryBindInterfaceRef(const ASTContext& context,
                                           const ExpressionSyntax& syntax, bool isInterfacePort);

    /// Specialized method for creating all of the expressions in a set membership check.
    /// This is used for case statements and the 'inside' operator.
    ///
    /// @param context The context used for creating expressions.
    /// @param valueExpr The value being checked for membership.
    /// @param expressions Denotes the set to check within. All of the expressions influence
    /// each other for purposes of finding a common comparison type.
    ///
    /// @param keyword The kind of membership being created, which is used to customize
    /// any diagnostics produced.
    ///
    /// @param requireIntegral If set to true, expression types will be restricted to
    /// be only integral types.
    ///
    /// @param unwrapUnpacked If set to true, unpacked arrays will be unwrapped to
    /// their element types to find the type to check against. Otherwise, all aggregates
    /// are illegal.
    ///
    /// @param allowOpenRange If set to true, open range expressions will be allowed.
    /// Otherwise an error will be issued for them.
    ///
    /// @param allowTypeReferences If set to true the created expressions are allowed to
    /// be type reference expressions. Otherwise an error will be issued.
    ///
    /// @param results A vector that will be filled with the created membership expressions.
    ///
    /// @returns true if all expressions are legal, otherwise false and appropriate
    /// diagnostics are issued.
    static bool bindMembershipExpressions(const ASTContext& context, parsing::TokenKind keyword,
                                          bool requireIntegral, bool unwrapUnpacked,
                                          bool allowTypeReferences, bool allowOpenRange,
                                          const ExpressionSyntax& valueExpr,
                                          span<const ExpressionSyntax* const> expressions,
                                          SmallVectorBase<const Expression*>& results);

    /// This method finds all unqualified name references in the given expression and attempts
    /// to look them up in the given context. If they can't be found, their name tokens are
    /// returned in the given @a results vector.
    static void findPotentiallyImplicitNets(
        const syntax::SyntaxNode& expr, const ASTContext& context,
        SmallVectorBase<const syntax::IdentifierNameSyntax*>& results);

    /// Converts an expression to be of the given type, following the rules for
    /// implicit conversions, array port slicing, etc.
    static Expression& convertAssignment(const ASTContext& context, const Type& type,
                                         Expression& expr, SourceLocation location,
                                         Expression** lhsExpr = nullptr,
                                         bitmask<AssignFlags>* assignFlags = nullptr);

    /// Indicates whether the expression is invalid.
    bool bad() const;

    /// Indicates whether the expression is of type string, or if it
    /// is implicitly convertible to a string.
    bool isImplicitString() const;

    /// Indicates whether the expression is represented by an unsized integer value.
    /// For example, the integer literal "4" or the unbased unsized literal "'1";
    bool isUnsizedInteger() const;

    /// Evaluates the expression under the given evaluation context. Any errors that occur
    /// will be stored in the evaluation context instead of issued to the compilation.
    ConstantValue eval(EvalContext& context) const;

    /// Evaluates the expression as an lvalue. Note that this will throw an exception
    /// if the expression does not represent an lvalue.
    LValue evalLValue(EvalContext& context) const;

    /// Evaluates the expression as a selector and returns the selection range that
    /// results. If the evaluates fails or the expression does not represent a selection
    /// std::nullopt will be returned.
    std::optional<ConstantRange> evalSelector(EvalContext& context) const;

    /// Verifies that this expression is a valid lvalue and that each element
    /// of that lvalue can be assigned to. If it's not, appropriate diagnostics
    /// will be issued. Information about the source expression driving the lvalue
    /// will be registered with the various symbols involved.
    bool requireLValue(const ASTContext& context, SourceLocation location = {},
                       bitmask<AssignFlags> flags = {},
                       const Expression* longestStaticPrefix = nullptr) const;

    /// If this expression is a valid lvalue, returns the part(s) of it that
    /// constitutes the "longest static prefix" for purposes of determining
    /// duplicate assignments / drivers to a portion of a value, for each
    /// such lvalue (usually one unless there is an lvalue concatenation).
    /// If there are no lvalues the vector will not have any entries added to it.
    void getLongestStaticPrefixes(
        SmallVector<std::pair<const ValueSymbol*, const Expression*>>& results,
        EvalContext& evalContext, const Expression* longestStaticPrefix = nullptr) const;

    /// Checks whether this kind of expression can be connected to a ref argument
    /// for a subroutine or module port.
    bool canConnectToRefArg(bool isConstRef, bool allowConstClassHandle = false) const;

    /// Returns true if this expression can be implicitly assigned to value
    /// of the given type.
    bool isImplicitlyAssignableTo(Compilation& compilation, const Type& type) const;

    /// Traverses the expression tree and computes what its width would be (in bits)
    /// if the types of all known constants were declared with only the bits necessary to
    /// represent them. If any encountered expressions have errors, returns nullopt.
    std::optional<bitwidth_t> getEffectiveWidth() const;

    /// If this expression is a reference to a symbol, returns a pointer to that symbol.
    /// Otherwise, returns null. If the expression is a member access of a struct
    /// or class, returns the member being accessed. If it's a select of an array, returns
    /// the root array variable. The @a allowPacked argument determines whether selects
    /// of a packed type are considered a symbol reference or whether to consider only
    /// unpacked structs and arrays.
    const Symbol* getSymbolReference(bool allowPacked = true) const;

    /// Returns true if any subexpression of this expression is a hierarchical reference.
    bool hasHierarchicalReference() const;

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

    template<typename T>
    T* as_if() {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<T*>(this);
    }

    template<typename T>
    const T* as_if() const {
        if (!T::isKind(kind))
            return nullptr;
        return static_cast<const T*>(this);
    }

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor&& visitor, Args&&... args);

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor&& visitor, Args&&... args) const;

protected:
    Expression(ExpressionKind kind, const Type& type, SourceRange sourceRange) :
        kind(kind), type(&type), sourceRange(sourceRange) {}

    static UnaryOperator getUnaryOperator(syntax::SyntaxKind kind);
    static BinaryOperator getBinaryOperator(syntax::SyntaxKind kind);

    static const Type* binaryOperatorType(Compilation& compilation, const Type* lt, const Type* rt,
                                          bool forceFourState, bool signednessFromRt = false);

    static ConstantValue evalBinaryOperator(BinaryOperator op, const ConstantValue& cvl,
                                            const ConstantValue& cvr);

    static Expression& create(Compilation& compilation, const ExpressionSyntax& syntax,
                              const ASTContext& context,
                              bitmask<ASTFlags> extraFlags = ASTFlags::None,
                              const Type* assignmentTarget = nullptr);

    static Expression& bindName(Compilation& compilation, const syntax::NameSyntax& syntax,
                                const syntax::InvocationExpressionSyntax* invocation,
                                const syntax::ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                const ASTContext& context);

    static Expression& bindLookupResult(
        Compilation& compilation, LookupResult& result, SourceRange sourceRange,
        const syntax::InvocationExpressionSyntax* invocation,
        const syntax::ArrayOrRandomizeMethodExpressionSyntax* withClause,
        const ASTContext& context);

    static Expression& bindSelectExpression(Compilation& compilation,
                                            const syntax::ElementSelectExpressionSyntax& syntax,
                                            const ASTContext& context);
    static Expression& bindSelector(Compilation& compilation, Expression& value,
                                    const syntax::ElementSelectSyntax& syntax,
                                    const ASTContext& context);

    static Expression& bindAssignmentPattern(
        Compilation& compilation, const syntax::AssignmentPatternExpressionSyntax& syntax,
        const ASTContext& context, const Type* assignmentTarget);

    static Expression* tryConnectPortArray(const ASTContext& context, const Type& type,
                                           Expression& expr, const InstanceSymbolBase& instance);

    static Expression& badExpr(Compilation& compilation, const Expression* expr);

    // Perform type propagation and constant folding of a context-determined subexpression.
    static void contextDetermined(const ASTContext& context, Expression*& expr, const Type& newType,
                                  SourceLocation assignmentLoc = {});

    // Perform type propagation and constant folding of a self-determined subexpression.
    static void selfDetermined(const ASTContext& context, Expression*& expr);
    [[nodiscard]] static Expression& selfDetermined(Compilation& compilation,
                                                    const ExpressionSyntax& syntax,
                                                    const ASTContext& context,
                                                    bitmask<ASTFlags> extraFlags = ASTFlags::None);
    struct PropagationVisitor;

    template<typename TExpression, typename TVisitor, typename... Args>
    decltype(auto) visitExpression(TExpression* expr, TVisitor&& visitor, Args&&... args) const;

    using NamedArgMap =
        SmallMap<string_view, std::pair<const syntax::NamedArgumentSyntax*, bool>, 8>;
    static bool collectArgs(const ASTContext& context, const syntax::ArgumentListSyntax& syntax,
                            SmallVectorBase<const syntax::SyntaxNode*>& orderedArgs,
                            NamedArgMap& namedArgs);
};

/// Represents an invalid expression, which is usually generated and inserted
/// into an expression tree due to violation of language semantics or type checking.
class SLANG_EXPORT InvalidExpression : public Expression {
public:
    /// A wrapped sub-expression that is considered invalid.
    const Expression* child;

    InvalidExpression(const Expression* child, const Type& type) :
        Expression(ExpressionKind::Invalid, type, SourceRange()), child(child) {}

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Invalid; }

    static const InvalidExpression Instance;
};

} // namespace slang::ast
