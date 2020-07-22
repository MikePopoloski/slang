//------------------------------------------------------------------------------
//! @file Expression.h
//! @brief Expression creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/BindContext.h"
#include "slang/binding/EvalContext.h"
#include "slang/symbols/SemanticFacts.h"

namespace slang {

class ASTSerializer;
class InstanceSymbol;
class Type;
struct AssignmentPatternExpressionSyntax;
struct ElementSelectExpressionSyntax;
struct ExpressionSyntax;
struct InvocationExpressionSyntax;

// clang-format off
#define EXPRESSION(x) \
    x(Invalid) \
    x(IntegerLiteral) \
    x(RealLiteral) \
    x(TimeLiteral) \
    x(UnbasedUnsizedIntegerLiteral) \
    x(NullLiteral) \
    x(StringLiteral) \
    x(NamedValue) \
    x(UnaryOp) \
    x(BinaryOp) \
    x(ConditionalOp) \
    x(Inside) \
    x(Assignment) \
    x(Concatenation) \
    x(Replication) \
    x(ElementSelect) \
    x(RangeSelect) \
    x(MemberAccess) \
    x(Call) \
    x(Conversion) \
    x(DataType) \
    x(SimpleAssignmentPattern) \
    x(StructuredAssignmentPattern) \
    x(ReplicatedAssignmentPattern) \
    x(EmptyArgument) \
    x(OpenRange)
ENUM(ExpressionKind, EXPRESSION);
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
ENUM(UnaryOperator, OP);
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
ENUM(BinaryOperator, OP);
#undef OP

#define RANGE(x) x(Simple) x(IndexedUp) x(IndexedDown)
ENUM(RangeSelectionKind, RANGE);
#undef RANGE
// clang-format on

/// The base class for all expressions in SystemVerilog.
class Expression {
public:
    /// The kind of expression; indicates the type of derived class.
    ExpressionKind kind;

    /// The type of the expression.
    not_null<const Type*> type;

    /// The syntax used to create the expression, if any. An expression tree can
    /// be created manually in which case it may not have a syntax representation.
    const ExpressionSyntax* syntax = nullptr;

    /// The source range of this expression, if it originated from source code.
    SourceRange sourceRange;

    /// Binds an expression tree from the given syntax nodes.
    static const Expression& bind(const ExpressionSyntax& syntax, const BindContext& context,
                                  bitmask<BindFlags> extraFlags = BindFlags::None);

    /// Binds the left hand side of an assignment-like expression from the given syntax nodes.
    static const Expression& bindLValue(const ExpressionSyntax& lhs, const Type& rhs,
                                        SourceLocation location, const BindContext& context);

    /// Binds the right hand side of an assignment-like expression from the given syntax nodes.
    static const Expression& bindRValue(const Type& lhs, const ExpressionSyntax& rhs,
                                        SourceLocation location, const BindContext& context);

    /// Binds an argument or port connection with the given direction and syntax nodes.
    static const Expression& bindArgument(const Type& argType, ArgumentDirection direction,
                                          const ExpressionSyntax& syntax,
                                          const BindContext& context);

    /// Binds an initializer expression for an implicitly typed parameter.
    /// There are special inference rules for parameters.
    static const Expression& bindImplicitParam(const DataTypeSyntax& implicitType,
                                               const ExpressionSyntax& rhs, SourceLocation location,
                                               const BindContext& context);

    /// Converts the given expression to the specified type, as if the right hand side had been
    /// assigned (without a cast) to a left hand side of the specified type.
    static Expression& convertAssignment(const BindContext& context, const Type& type,
                                         Expression& expr, SourceLocation location,
                                         optional<SourceRange> lhsRange = std::nullopt);

    /// Specialized method for binding all of the expressions in a set membership check.
    /// This is used for case statements and the 'inside' operator.
    ///
    /// The @param valueExpr is the value being checked for membership, and @param expressions
    /// denotes the set to check within. All of the expressions influence each other for
    /// purposes of finding a common comparison type.
    ///
    /// The @param keyword parameter is used to customize diagnostics produced.
    ///
    /// If @param wildcard is set to true, expression types will be restricted to
    /// be only integral types.
    ///
    /// If @param unwrapUnpacked is set to true, unpacked arrays will be unwrapped to
    /// their element types to find the type to check against. Otherwise, all aggregates
    /// are illegal.
    ///
    /// @returns true if all expressions are legal, otherwise false and appropriate
    /// diagnostics are issued.
    static bool bindMembershipExpressions(const BindContext& context, TokenKind keyword,
                                          bool wildcard, bool unwrapUnpacked,
                                          const ExpressionSyntax& valueExpr,
                                          span<const ExpressionSyntax* const> expressions,
                                          SmallVector<const Expression*>& results);

    /// This method finds all unqualified name references in the given expression and attempts
    /// to look them up in the given context. If they can't be found, their name tokens are
    /// returned in the given @a results vector.
    static void findPotentiallyImplicitNets(const ExpressionSyntax& expr,
                                            const BindContext& context,
                                            SmallVector<Token>& results);

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

    /// Evaluates an expression as an lvalue. Note that this will throw an exception
    /// if the expression does not represent an lvalue.
    LValue evalLValue(EvalContext& context) const;

    /// Verifies that this expression is valid as a constant expression.
    /// If it's not, appropriate diagnostics will be issued.
    bool verifyConstant(EvalContext& context) const;

    /// Verifies that this expression is a valid lvalue and that each element
    /// of that lvalue can be assigned to. If it's not, appropriate diagnostics
    /// will be issued.
    bool verifyAssignable(const BindContext& context, bool isNonBlocking = false,
                          SourceLocation location = {}) const;

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
    decltype(auto) visit(TVisitor&& visitor, Args&&... args);

    template<typename TVisitor, typename... Args>
    decltype(auto) visit(TVisitor&& visitor, Args&&... args) const;

protected:
    Expression(ExpressionKind kind, const Type& type, SourceRange sourceRange) :
        kind(kind), type(&type), sourceRange(sourceRange) {}

    static UnaryOperator getUnaryOperator(SyntaxKind kind);
    static BinaryOperator getBinaryOperator(SyntaxKind kind);

    static const Type* binaryOperatorType(Compilation& compilation, const Type* lt, const Type* rt,
                                          bool forceFourState);

    static ConstantValue evalBinaryOperator(BinaryOperator op, const ConstantValue& cvl,
                                            const ConstantValue& cvr);

    static const Expression& checkBindFlags(const Expression& expr, const BindContext& context);

    static Expression& create(Compilation& compilation, const ExpressionSyntax& syntax,
                              const BindContext& context,
                              bitmask<BindFlags> extraFlags = BindFlags::None,
                              const Type* assignmentTarget = nullptr);
    static Expression& implicitConversion(const BindContext& context, const Type& type,
                                          Expression& expr);

    static Expression& bindName(Compilation& compilation, const NameSyntax& syntax,
                                const InvocationExpressionSyntax* invocation,
                                const BindContext& context);
    static Expression& bindSelectExpression(Compilation& compilation,
                                            const ElementSelectExpressionSyntax& syntax,
                                            const BindContext& context);
    static Expression& bindSelector(Compilation& compilation, Expression& value,
                                    const ElementSelectSyntax& syntax, const BindContext& context);

    static Expression& bindAssignmentPattern(Compilation& compilation,
                                             const AssignmentPatternExpressionSyntax& syntax,
                                             const BindContext& context,
                                             const Type* assignmentTarget);

    static Expression* tryConnectPortArray(const BindContext& context, const Type& type,
                                           Expression& expr, const InstanceSymbol& instance);

    static Expression& badExpr(Compilation& compilation, const Expression* expr);

    // Perform type propagation and constant folding of a context-determined subexpression.
    static void contextDetermined(const BindContext& context, Expression*& expr,
                                  const Type& newType);

    // Perform type propagation and constant folding of a self-determined subexpression.
    static void selfDetermined(const BindContext& context, Expression*& expr);
    [[nodiscard]] static Expression& selfDetermined(
        Compilation& compilation, const ExpressionSyntax& syntax, const BindContext& context,
        bitmask<BindFlags> extraFlags = BindFlags::None);
    struct PropagationVisitor;

    template<typename TExpression, typename TVisitor, typename... Args>
    decltype(auto) visitExpression(TExpression* expr, TVisitor&& visitor, Args&&... args) const;
};

/// Represents an invalid expression, which is usually generated and inserted
/// into an expression tree due to violation of language semantics or type checking.
class InvalidExpression : public Expression {
public:
    /// A wrapped sub-expression that is considered invalid.
    const Expression* child;

    InvalidExpression(const Expression* child, const Type& type) :
        Expression(ExpressionKind::Invalid, type, SourceRange()), child(child) {}

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Invalid; }

    static const InvalidExpression Instance;
};

} // namespace slang
