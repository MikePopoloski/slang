//------------------------------------------------------------------------------
// Expressions.h
// Expression creation and analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "EvalContext.h"

namespace slang {

struct ExpressionSyntax;

enum class ExpressionKind {
    Invalid,
    Literal,
    VariableRef,
    ParameterRef,
    UnaryOp,
    BinaryOp,
    TernaryOp,
    NaryOp,
    Select,
    Call
};

enum class LiteralKind {
    UnbasedUnsizedInteger,
    Other
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
    LogicalNot
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
    Power,
    Replication,
    Assignment,
    AddAssignment,
    SubtractAssignment,
    MultiplyAssignment,
    DivideAssignment,
    ModAssignment,
    AndAssignment,
    OrAssignment,
    XorAssignment,
    LogicalLeftShiftAssignment,
    LogicalRightShiftAssignment,
    ArithmeticLeftShiftAssignment,
    ArithmeticRightShiftAssignment,
};

LiteralKind getLiteralKind(const ExpressionSyntax& syntax);
UnaryOperator getUnaryOperator(const ExpressionSyntax& syntax);
BinaryOperator getBinaryOperator(const ExpressionSyntax& syntax);

/// The base class for all expressions in SystemVerilog.
class Expression {
public:    
    /// The kind of expression; indicates the type of derived class.
    ExpressionKind kind;

    /// The syntax used to create this expression, if it was parsed from a source file.
    const ExpressionSyntax* syntax;

    /// The type of the expression.
    const TypeSymbol* type;

    /// Indicates whether the expression is invalid.
    bool bad() const { return kind == ExpressionKind::Invalid; }

    /// Propagates the type of the expression down to its children,
    /// according to the rules laid out in the standard.
    void propagateType(const TypeSymbol& newType);

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
    const T& as() const { return *static_cast<const T*>(this); }

    template<typename T>
    T& as() { return *static_cast<T*>(this); }

protected:
    Expression(ExpressionKind kind, const TypeSymbol& type) :
        kind(kind), syntax(nullptr), type(&type) {}
    Expression(ExpressionKind kind, const TypeSymbol& type, const ExpressionSyntax& syntax) :
        kind(kind), syntax(&syntax), type(&type) {}
};

/// Represents an invalid expression, which is usually generated and inserted
/// into an expression tree due to violation of language semantics or type checking.
class InvalidExpression : public Expression {
public:
    /// A wrapped sub-expression that is considered invalid.
    const Expression* child;

    InvalidExpression(const Expression* child, const TypeSymbol& type) :
        Expression(ExpressionKind::Invalid, type), child(child) {}
};

/// Represents a literal expression.
class LiteralExpression : public Expression {
public:
    LiteralKind literalKind;
    ConstantValue value;

    LiteralExpression(const TypeSymbol& type, const ConstantValue& value, const ExpressionSyntax& syntax) :
        Expression(ExpressionKind::Literal, type, syntax),
        literalKind(getLiteralKind(syntax)), value(value) {}
    
    void propagateType(const TypeSymbol& newType);
    ConstantValue eval(EvalContext& context) const;
};

/// Represents an expression that references a variable.
class VariableRefExpression : public Expression {
public:
    const VariableSymbol& symbol;

    VariableRefExpression(const VariableSymbol& symbol, const ExpressionSyntax& syntax) :
        Expression(ExpressionKind::VariableRef, symbol.type(), syntax), symbol(symbol) {}

    ConstantValue eval(EvalContext& context) const;
};

/// Represents an expression that references a parameter.
class ParameterRefExpression : public Expression {
public:
    const ParameterSymbol& symbol;

    ParameterRefExpression(const ParameterSymbol& symbol, const ExpressionSyntax& syntax) :
        Expression(ExpressionKind::ParameterRef, symbol.type(), syntax), symbol(symbol) {}

    ConstantValue eval(EvalContext& context) const;
};

/// Represents a unary operator expression.
class UnaryExpression : public Expression {
public:
    UnaryOperator op;

    UnaryExpression(const TypeSymbol& type, Expression& operand, const ExpressionSyntax& syntax) :
        Expression(ExpressionKind::UnaryOp, type, syntax),
        op(getUnaryOperator(syntax)), operand_(&operand) {}

    const Expression& operand() const { return *operand_; }
    Expression& operand() { return *operand_; }

    void propagateType(const TypeSymbol& newType);
    ConstantValue eval(EvalContext& context) const;

private:
    Expression* operand_;
};

/// Represents a binary operator expression.
class BinaryExpression : public Expression {
public:
    BinaryOperator op;

    BinaryExpression(const TypeSymbol& type, Expression& left, Expression& right, const ExpressionSyntax& syntax) :
        Expression(ExpressionKind::BinaryOp, type, syntax),
        op(getBinaryOperator(syntax)), left_(&left), right_(&right) {}

    bool isAssignment() const;

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    void propagateType(const TypeSymbol& newType);
    ConstantValue eval(EvalContext& context) const;

private:
    Expression* left_;
    Expression* right_;
};

/// Represents a ternary operator expression (only the conditional operator is ternary).
class TernaryExpression : public Expression {
public:
    TernaryExpression(const TypeSymbol& type, Expression& pred, Expression& left, Expression& right, const ExpressionSyntax& syntax) :
        Expression(ExpressionKind::TernaryOp, type, syntax), pred_(&pred), left_(&left), right_(&right) {}

    const Expression& pred() const { return *pred_; }
    Expression& pred() { return *pred_; }

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    void propagateType(const TypeSymbol& newType);
    ConstantValue eval(EvalContext& context) const;

private:
    Expression* pred_;
    Expression* left_;
    Expression* right_;
};

/// Represents a variable selection expression.
class SelectExpression : public Expression {
public:
    // TODO: get rid of this
    SyntaxKind kind;

    SelectExpression(const TypeSymbol& type, SyntaxKind kind, Expression& expr, Expression& left,
                     Expression& right, const ExpressionSyntax& syntax) :
        Expression(ExpressionKind::Select, type, syntax), kind(kind),
        expr_(&expr), left_(&left), right_(&right) {}

    const Expression& expr() const { return *expr_; }
    Expression& expr() { return *expr_; }

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue eval(EvalContext& context) const;

private:
    Expression* expr_;
    Expression* left_;
    Expression* right_;
};

/// Represents an expression of unbounded arity (for example, concatenations).
class NaryExpression : public Expression {
public:
    NaryExpression(const TypeSymbol& type, span<const Expression*> operands, const ExpressionSyntax& syntax) :
        Expression(ExpressionKind::NaryOp, type, syntax), operands_(operands) {}

    span<const Expression* const> operands() const { return operands_; }
    span<const Expression*> operands() { return operands_; }

    ConstantValue eval(EvalContext& context) const;

private:
    span<const Expression*> operands_;
};

/// Represents a subroutine call.
class CallExpression : public Expression {
public:
    const SubroutineSymbol& subroutine;

    CallExpression(const SubroutineSymbol& subroutine, span<const Expression*> arguments, const ExpressionSyntax& syntax) :
        Expression(ExpressionKind::Call, subroutine.returnType(), syntax),
        subroutine(subroutine), arguments_(arguments) {}

    span<const Expression* const> arguments() const { return arguments_; }
    span<const Expression*> arguments() { return arguments_; }

    ConstantValue eval(EvalContext& context) const;

private:
    span<const Expression*> arguments_;
};

}