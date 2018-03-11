//------------------------------------------------------------------------------
// Expressions.h
// Expression creation and analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "binding/BindContext.h"
#include "binding/EvalContext.h"
#include "symbols/MemberSymbols.h"
#include "symbols/TypeSymbols.h"

namespace slang {

struct ExpressionSyntax;

enum class ExpressionKind {
    Invalid,
    IntegerLiteral,
    RealLiteral,
    UnbasedUnsizedIntegerLiteral,
    NullLiteral,
    StringLiteral,
    NamedValue,
    UnaryOp,
    BinaryOp,
    ConditionalOp,
    Assignment,
    Concatenation,
    Replication,
    ElementSelect,
    RangeSelect,
    MemberAccess,
    Call,
    Conversion,
};

enum class UnaryOperator {
    Plus,
    Minus,
    BitwiseNot,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    BitwiseNand,
    BitwiseNor,
    BitwiseXnor,
    LogicalNot,
    Preincrement,
    Predecrement,
    Postincrement,
    Postdecrement
};

enum class BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Mod,
    BinaryAnd,
    BinaryOr,
    BinaryXor,
    BinaryXnor,
    Equality,
    Inequality,
    CaseEquality,
    CaseInequality,
    GreaterThanEqual,
    GreaterThan,
    LessThanEqual,
    LessThan,
    WildcardEquality,
    WildcardInequality,
    LogicalAnd,
    LogicalOr,
    LogicalImplication,
    LogicalEquivalence,
    LogicalShiftLeft,
    LogicalShiftRight,
    ArithmeticShiftLeft,
    ArithmeticShiftRight,
    Power
};

enum class RangeSelectionKind {
    Simple,
    IndexedUp,
    IndexedDown
};

enum class ConversionKind {
    IntToFloat,
    IntExtension,
    FloatExtension
};

UnaryOperator getUnaryOperator(SyntaxKind kind);
BinaryOperator getBinaryOperator(SyntaxKind kind);

/// The base class for all expressions in SystemVerilog.
class Expression {
public:
    /// The kind of expression; indicates the type of derived class.
    ExpressionKind kind;

    /// The type of the expression.
    not_null<const Type*> type;

    /// The value of the expression, if it's constant. Otherwise nullptr.
    const ConstantValue* constant = nullptr;

    /// The source range of this expression, if it originated from source code.
    SourceRange sourceRange;

    /// Binds an expression tree from the given syntax nodes.
    static const Expression& bind(Compilation& compilation, const ExpressionSyntax& syntax,
                                  const BindContext& context);

    /// Binds an assignment-like expression from the given syntax nodes.
    static const Expression& bind(Compilation& compilation, const Type& lhs, const ExpressionSyntax& rhs,
                                  SourceLocation location, const BindContext& context);

    /// Indicates whether the expression is invalid.
    bool bad() const;

    /// Indicates whether the expression evaluates to an lvalue.
    bool isLValue() const;

    /// Evaluates the expression under the given evaluation context.
    ConstantValue eval(EvalContext& context) const;

    /// Evaluates the expression under a default context.
    ConstantValue eval() const {
        EvalContext context;
        return eval(context);
    }

    /// Evaluates the expression and tries to interpret the result in a boolean context.
    bool evalBool(EvalContext& context) const;

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

protected:
    Expression(ExpressionKind kind, const Type& type, SourceRange sourceRange) :
        kind(kind), type(&type), sourceRange(sourceRange) {}

    static Expression& create(Compilation& compilation, const ExpressionSyntax& syntax, const BindContext& context);
    static Expression& convert(Compilation& compilation, ConversionKind conversionKind, const Type& type, Expression& expr);

    static Expression& bindName(Compilation& compilation, const NameSyntax& syntax, const BindContext& context);
    static Expression& bindSelectExpression(Compilation& compilation, const ElementSelectExpressionSyntax& syntax, const BindContext& context);
    static Expression& bindSelector(Compilation& compilation, Expression& value, const ElementSelectSyntax& syntax, const BindContext& context);

    static Expression& badExpr(Compilation& compilation, const Expression* expr);

    // Perform type propagation and constant folding of a context-determined subexpression.
    static void contextDetermined(Compilation& compilation, Expression*& expr, const Type& newType);

    // Perform type propagation and constant folding of a self-determined subexpression.
    static void selfDetermined(Compilation& compilation, Expression*& expr);
    [[nodiscard]] static Expression& selfDetermined(Compilation& compilation, const ExpressionSyntax& syntax,
                                                    const BindContext& context);

    // Helper methods for checking common expression requirements.
    static bool checkLValue(Compilation& compilation, const Expression& expr, SourceLocation location);

    struct PropagationVisitor;
};

/// Represents an invalid expression, which is usually generated and inserted
/// into an expression tree due to violation of language semantics or type checking.
class InvalidExpression : public Expression {
public:
    /// A wrapped sub-expression that is considered invalid.
    const Expression* child;

    InvalidExpression(const Expression* child, const Type& type) :
        Expression(ExpressionKind::Invalid, type, SourceRange()), child(child) {}

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Invalid; }

    static const InvalidExpression Instance;
};

/// Represents an integer literal.
class IntegerLiteral : public Expression {
public:
    IntegerLiteral(BumpAllocator& alloc, const Type& type, const SVInt& value, SourceRange sourceRange);

    SVInt getValue() const { return valueStorage; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, const LiteralExpressionSyntax& syntax);
    static Expression& fromSyntax(Compilation& compilation, const IntegerVectorExpressionSyntax& syntax);
    static Expression& propagateType(Compilation& compilation, IntegerLiteral& expr, const Type& newType);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::IntegerLiteral; }

private:
    SVIntStorage valueStorage;
};

/// Represents a real number literal.
class RealLiteral : public Expression {
public:
    RealLiteral(const Type& type, double value, SourceRange sourceRange) :
        Expression(ExpressionKind::RealLiteral, type, sourceRange), value(value) {}

    double getValue() const { return value; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, const LiteralExpressionSyntax& syntax);
    static Expression& propagateType(Compilation& compilation, RealLiteral& expr, const Type& newType);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::RealLiteral; }

private:
    double value;
};

/// Represents an unbased unsized integer literal, which fills all bits in an expression.
class UnbasedUnsizedIntegerLiteral : public Expression {
public:
    UnbasedUnsizedIntegerLiteral(const Type& type, logic_t value, SourceRange sourceRange) :
        Expression(ExpressionKind::UnbasedUnsizedIntegerLiteral, type, sourceRange), value(value) {}

    logic_t getValue() const { return value; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, const LiteralExpressionSyntax& syntax);
    static Expression& propagateType(Compilation& compilation, UnbasedUnsizedIntegerLiteral& expr, const Type& newType);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::UnbasedUnsizedIntegerLiteral; }

private:
    logic_t value;
};

/// Represents a null literal.
class NullLiteral : public Expression {
public:
    NullLiteral(const Type& type, SourceRange sourceRange) :
        Expression(ExpressionKind::NullLiteral, type, sourceRange) {}

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, const LiteralExpressionSyntax& syntax);
    static Expression& propagateType(Compilation& compilation, NullLiteral& expr, const Type& newType);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::NullLiteral; }
};

/// Represents a string literal.
class StringLiteral : public Expression {
public:
    StringLiteral(const Type& type, string_view value, SourceRange sourceRange) :
        Expression(ExpressionKind::StringLiteral, type, sourceRange), value(value) {}

    string_view getValue() const { return value; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, const LiteralExpressionSyntax& syntax);
    static Expression& propagateType(Compilation& compilation, StringLiteral& expr, const Type& newType);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::StringLiteral; }

private:
    string_view value;
};

/// Represents an expression that references a named value.
class NamedValueExpression : public Expression {
public:
    const ValueSymbol& symbol;

    NamedValueExpression(const ValueSymbol& symbol, SourceRange sourceRange) :
        Expression(ExpressionKind::NamedValue, symbol.getType(), sourceRange), symbol(symbol) {}

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& propagateType(Compilation& compilation, NamedValueExpression& expr, const Type& newType);
    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::NamedValue; }
};

/// Represents a unary operator expression.
class UnaryExpression : public Expression {
public:
    UnaryOperator op;

    UnaryExpression(UnaryOperator op, const Type& type, Expression& operand, SourceRange sourceRange) :
        Expression(ExpressionKind::UnaryOp, type, sourceRange),
        op(op), operand_(&operand) {}

    const Expression& operand() const { return *operand_; }
    Expression& operand() { return *operand_; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, const PrefixUnaryExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& fromSyntax(Compilation& compilation, const PostfixUnaryExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& propagateType(Compilation& compilation, UnaryExpression& expr, const Type& newType);
    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::UnaryOp; }

private:
    Expression* operand_;
};

/// Represents a binary operator expression.
class BinaryExpression : public Expression {
public:
    BinaryOperator op;

    BinaryExpression(BinaryOperator op, const Type& type, Expression& left, Expression& right, SourceRange sourceRange) :
        Expression(ExpressionKind::BinaryOp, type, sourceRange),
        op(op), left_(&left), right_(&right) {}

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, const BinaryExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& propagateType(Compilation& compilation, BinaryExpression& expr, const Type& newType);
    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::BinaryOp; }

private:
    Expression* left_;
    Expression* right_;
};

/// Represents a conditional operator expression.
class ConditionalExpression : public Expression {
public:
    ConditionalExpression(const Type& type, Expression& pred, Expression& left,
                          Expression& right, SourceRange sourceRange) :
        Expression(ExpressionKind::ConditionalOp, type, sourceRange),
        pred_(&pred), left_(&left), right_(&right) {}

    const Expression& pred() const { return *pred_; }
    Expression& pred() { return *pred_; }

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, const ConditionalExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& propagateType(Compilation& compilation, ConditionalExpression& expr, const Type& newType);
    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::ConditionalOp; }

private:
    Expression* pred_;
    Expression* left_;
    Expression* right_;
};

/// Represents an assignment expression.
class AssignmentExpression : public Expression {
public:
    optional<BinaryOperator> op;

    AssignmentExpression(optional<BinaryOperator> op, const Type& type, Expression& left,
                         Expression& right, SourceRange sourceRange) :
        Expression(ExpressionKind::Assignment, type, sourceRange),
        op(op), left_(&left), right_(&right) {}

    bool isCompound() const { return op.has_value(); }

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, const BinaryExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& propagateType(Compilation& compilation, AssignmentExpression& expr, const Type& newType);
    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Assignment; }

private:
    Expression* left_;
    Expression* right_;
};

/// Represents a single element selection expression.
class ElementSelectExpression : public Expression {
public:
    ElementSelectExpression(const Type& type, Expression& value, Expression& selector, SourceRange sourceRange) :
        Expression(ExpressionKind::ElementSelect, type, sourceRange),
        value_(&value), selector_(&selector) {}

    const Expression& value() const { return *value_; }
    Expression& value() { return *value_; }

    const Expression& selector() const { return *selector_; }
    Expression& selector() { return *selector_; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, Expression& value, const ExpressionSyntax& syntax,
                                  SourceRange fullRange, const BindContext& context);
    static Expression& propagateType(Compilation& compilation, ElementSelectExpression& expr, const Type& newType);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::ElementSelect; }

private:
    Expression* value_;
    Expression* selector_;
};

/// Represents a range selection expression.
class RangeSelectExpression : public Expression {
public:
    RangeSelectionKind selectionKind;

    RangeSelectExpression(RangeSelectionKind selectionKind, const Type& type, Expression& value,
                          Expression& left, Expression& right, SourceRange sourceRange) :
        Expression(ExpressionKind::RangeSelect, type, sourceRange),
        selectionKind(selectionKind), value_(&value), left_(&left), right_(&right) {}

    const Expression& value() const { return *value_; }
    Expression& value() { return *value_; }

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, Expression& value, const RangeSelectSyntax& syntax,
                                  SourceRange fullRange, const BindContext& context);
    static Expression& propagateType(Compilation& compilation, RangeSelectExpression& expr, const Type& newType);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::RangeSelect; }

private:
    Expression* value_;
    Expression* left_;
    Expression* right_;
};

/// Represents an access of a structure variable's members.
class MemberAccessExpression : public Expression {
public:
    const FieldSymbol& field;

    MemberAccessExpression(const Type& type, Expression& value, const FieldSymbol& field, SourceRange sourceRange) :
        Expression(ExpressionKind::MemberAccess, type, sourceRange),
        field(field), value_(&value) {}

    const Expression& value() const { return *value_; }
    Expression& value() { return *value_; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& propagateType(Compilation&, MemberAccessExpression& expr, const Type&) { return expr; }

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::MemberAccess; }

private:
    Expression* value_;
};

/// Represents a concatenation expression.
class ConcatenationExpression : public Expression {
public:
    ConcatenationExpression(const Type& type, span<const Expression*> operands, SourceRange sourceRange) :
        Expression(ExpressionKind::Concatenation, type, sourceRange), operands_(operands) {}

    span<const Expression* const> operands() const { return operands_; }
    span<const Expression*> operands() { return operands_; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, const ConcatenationExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& propagateType(Compilation& compilation, ConcatenationExpression& expr, const Type& newType);
    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Concatenation; }

private:
    span<const Expression*> operands_;
};

/// Represents a replication expression.
class ReplicationExpression : public Expression {
public:
    ReplicationExpression(const Type& type, Expression& count, Expression& concat, SourceRange sourceRange) :
        Expression(ExpressionKind::Replication, type, sourceRange),
        count_(&count), concat_(&concat) {}

    const Expression& count() const { return *count_; }
    Expression& count() { return *count_; }

    const Expression& concat() const { return *concat_; }
    Expression& concat() { return *concat_; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, const MultipleConcatenationExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& propagateType(Compilation& compilation, ReplicationExpression& expr, const Type& newType);
    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Replication; }

private:
    Expression* count_;
    Expression* concat_;
};

/// Represents a subroutine call.
class CallExpression : public Expression {
public:
    const SubroutineSymbol& subroutine;

    CallExpression(const SubroutineSymbol& subroutine, span<const Expression*> arguments, SourceRange sourceRange) :
        Expression(ExpressionKind::Call, *subroutine.returnType, sourceRange),
        subroutine(subroutine), arguments_(arguments) {}

    span<const Expression* const> arguments() const { return arguments_; }
    span<const Expression*> arguments() { return arguments_; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& fromSyntax(Compilation& compilation, const InvocationExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& propagateType(Compilation& compilation, CallExpression& expr, const Type& newType);
    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Call; }

private:
    span<const Expression*> arguments_;
};

/// Represents a type conversion expression.
class ConversionExpression : public Expression {
public:
    ConversionKind conversionKind;

    ConversionExpression(ConversionKind conversionKind, const Type& type, Expression& operand,
                         SourceRange sourceRange) :
        Expression(ExpressionKind::Conversion, type, sourceRange),
        conversionKind(conversionKind), operand_(&operand) {}

    const Expression& operand() const { return *operand_; }
    Expression& operand() { return *operand_; }

    ConstantValue evalImpl(EvalContext& context) const;

    static Expression& propagateType(Compilation& compilation, ConversionExpression& expr, const Type& newType);
    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Conversion; }

private:
    Expression* operand_;
};

}
