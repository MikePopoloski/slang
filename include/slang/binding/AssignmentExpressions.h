//------------------------------------------------------------------------------
//! @file AssignmentExpressions.h
//! @brief Definitions for assignment-related expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"

namespace slang {

class TimingControl;
struct BinaryExpressionSyntax;

/// Represents an assignment expression.
class AssignmentExpression : public Expression {
public:
    optional<BinaryOperator> op;
    const TimingControl* timingControl;

    AssignmentExpression(optional<BinaryOperator> op, bool nonBlocking, const Type& type,
                         Expression& left, Expression& right, const TimingControl* timingControl,
                         SourceRange sourceRange) :
        Expression(ExpressionKind::Assignment, type, sourceRange),
        op(op), timingControl(timingControl), left_(&left), right_(&right),
        nonBlocking(nonBlocking) {}

    bool isCompound() const { return op.has_value(); }
    bool isNonBlocking() const { return nonBlocking; }

    const Expression& left() const { return *left_; }
    Expression& left() { return *left_; }

    const Expression& right() const { return *right_; }
    Expression& right() { return *right_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const BinaryExpressionSyntax& syntax,
                                  const BindContext& context);

    static Expression& fromComponents(Compilation& compilation, optional<BinaryOperator> op,
                                      bool nonBlocking, Expression& lhs, Expression& rhs,
                                      SourceLocation assignLoc, const TimingControl* timingControl,
                                      SourceRange sourceRange, const BindContext& context);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Assignment; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        left().visit(visitor);
        right().visit(visitor);
    }

private:
    Expression* left_;
    Expression* right_;
    bool nonBlocking;
};

struct CastExpressionSyntax;
struct SignedCastExpressionSyntax;

enum class ConversionKind : uint8_t {
    Implicit,
    Propagated,
    StreamingConcat,
    Explicit,
    BitstreamCast
};

/// Represents a type conversion expression (implicit or explicit).
class ConversionExpression : public Expression {
public:
    const ConversionKind conversionKind;
    bool isImplicit() const { return conversionKind < ConversionKind::Explicit; }

    ConversionExpression(const Type& type, ConversionKind conversionKind, Expression& operand,
                         SourceRange sourceRange) :
        Expression(ExpressionKind::Conversion, type, sourceRange),
        conversionKind(conversionKind), operand_(&operand) {}

    const Expression& operand() const { return *operand_; }
    Expression& operand() { return *operand_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const CastExpressionSyntax& syntax,
                                  const BindContext& context);
    static Expression& fromSyntax(Compilation& compilation,
                                  const SignedCastExpressionSyntax& syntax,
                                  const BindContext& context);

    static ConstantValue convert(EvalContext& context, const Type& from, const Type& to,
                                 SourceRange sourceRange, ConstantValue&& value,
                                 ConversionKind conversionKind);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::Conversion; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        operand().visit(visitor);
    }

private:
    Expression* operand_;
};

struct NewArrayExpressionSyntax;

/// Represents a new[] expression that creates a dynamic array.
class NewArrayExpression : public Expression {
public:
    NewArrayExpression(const Type& type, const Expression& sizeExpr, const Expression* initializer,
                       SourceRange sourceRange) :
        Expression(ExpressionKind::NewArray, type, sourceRange),
        sizeExpr_(&sizeExpr), initializer_(initializer) {}

    const Expression& sizeExpr() const { return *sizeExpr_; }
    const Expression* initExpr() const { return initializer_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const NewArrayExpressionSyntax& syntax,
                                  const BindContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::NewArray; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        sizeExpr().visit(visitor);
        if (initExpr())
            initExpr()->visit(visitor);
    }

private:
    const Expression* sizeExpr_;
    const Expression* initializer_;
};

struct NewClassExpressionSyntax;

/// Represents a `new` expression that creates a class instance.
class NewClassExpression : public Expression {
public:
    /// Set to true if this is invoking a super class's constructor.
    bool isSuperClass = false;

    NewClassExpression(const Type& type, const Expression* constructorCall, bool isSuperClass,
                       SourceRange sourceRange) :
        Expression(ExpressionKind::NewClass, type, sourceRange),
        isSuperClass(isSuperClass), constructorCall_(constructorCall) {}

    const Expression* constructorCall() const { return constructorCall_; }

    ConstantValue evalImpl(EvalContext& context) const;
    bool verifyConstantImpl(EvalContext& context) const;

    void serializeTo(ASTSerializer& serializer) const;

    static Expression& fromSyntax(Compilation& compilation, const NewClassExpressionSyntax& syntax,
                                  const BindContext& context, const Type* assignmentTarget);

    static bool isKind(ExpressionKind kind) { return kind == ExpressionKind::NewClass; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        if (constructorCall())
            constructorCall()->visit(visitor);
    }

private:
    const Expression* constructorCall_;
};

} // namespace slang
