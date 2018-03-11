//------------------------------------------------------------------------------
// Expressions_prop.cpp
// Expression type propagation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Expressions.h"

#include "compilation/Compilation.h"
#include "symbols/ASTVisitor.h"

namespace slang {

struct Expression::PropagationVisitor {
    Compilation& compilation;
    const Type& newType;

    PropagationVisitor(Compilation& compilation, const Type& newType) :
        compilation(compilation), newType(newType) {}

    template<typename T>
    Expression& visit(T& expr) {
        if (expr.bad())
            return expr;

        // If we're propagating a floating type down to a non-floating type, that operand
        // will instead be converted in a self-determined context.
        if (newType.isFloating() && !expr.type->isFloating() && expr.kind != ExpressionKind::Conversion)
            return Expression::convert(compilation, ConversionKind::IntToFloat, newType, expr);

        // Perform type-specific propagation.
        Expression& result = T::propagateType(compilation, expr, newType);

        // Try to fold any constant values.
        ASSERT(!result.constant);
        ConstantValue value = result.eval();
        if (value)
            result.constant = compilation.createConstant(std::move(value));
        return result;
    }

    Expression& visitInvalid(Expression& expr) {
        return expr;
    }
};

void Expression::contextDetermined(Compilation& compilation, Expression*& expr, const Type& newType) {
    PropagationVisitor visitor(compilation, newType);
    expr = &expr->visit(visitor);
}

void Expression::selfDetermined(Compilation& compilation, Expression*& expr) {
    ASSERT(expr->type);
    PropagationVisitor visitor(compilation, *expr->type);
    expr = &expr->visit(visitor);
}

Expression& Expression::selfDetermined(Compilation& compilation, const ExpressionSyntax& syntax,
                                       const BindContext& context) {
    Expression* expr = &create(compilation, syntax, context);
    selfDetermined(compilation, expr);
    return *expr;
}

Expression& IntegerLiteral::propagateType(Compilation& compilation, IntegerLiteral& expr,
                                          const Type& newType) {
    ASSERT(newType.isIntegral());
    ASSERT(newType.getBitWidth() >= expr.type->getBitWidth());

    if (newType.getBitWidth() != expr.type->getBitWidth())
        return convert(compilation, ConversionKind::IntExtension, newType, expr);

    expr.type = &newType;
    return expr;
}

Expression& RealLiteral::propagateType(Compilation& compilation, RealLiteral& expr, const Type& newType) {
    ASSERT(newType.isFloating());
    ASSERT(newType.getBitWidth() >= expr.type->getBitWidth());

    if (newType.getBitWidth() != expr.type->getBitWidth())
        return convert(compilation, ConversionKind::FloatExtension, newType, expr);

    expr.type = &newType;
    return expr;
}

Expression& UnbasedUnsizedIntegerLiteral::propagateType(Compilation&,
                                                        UnbasedUnsizedIntegerLiteral& expr,
                                                        const Type& newType) {
    ASSERT(newType.isIntegral());
    ASSERT(newType.getBitWidth() >= expr.type->getBitWidth());

    expr.type = &newType;
    return expr;
}

Expression& NullLiteral::propagateType(Compilation&, NullLiteral& expr,
                                       const Type&) {
    return expr;
}

Expression& StringLiteral::propagateType(Compilation&, StringLiteral& expr,
                                         const Type& newType) {
    ASSERT(newType.isIntegral());
    ASSERT(newType.getBitWidth() >= expr.type->getBitWidth());

    // TODO:
    /*if (newType.getBitWidth() != expr.type->getBitWidth())
    return convert(compilation, ConversionKind::IntExtension, newType, expr);*/

    expr.type = &newType;
    return expr;
}

Expression& NamedValueExpression::propagateType(Compilation&, NamedValueExpression& expr,
                                                const Type&) {
    return expr;
}

Expression& UnaryExpression::propagateType(Compilation& compilation, UnaryExpression& expr,
                                           const Type& newType) {
    switch (expr.op) {
        case UnaryOperator::Plus:
        case UnaryOperator::Minus:
        case UnaryOperator::BitwiseNot:
            expr.type = &newType;
            contextDetermined(compilation, expr.operand_, newType);
            break;
        case UnaryOperator::BitwiseAnd:
        case UnaryOperator::BitwiseOr:
        case UnaryOperator::BitwiseXor:
        case UnaryOperator::BitwiseNand:
        case UnaryOperator::BitwiseNor:
        case UnaryOperator::BitwiseXnor:
        case UnaryOperator::LogicalNot:
            // Type is already set (always 1 bit).
            selfDetermined(compilation, expr.operand_);
            break;
        case UnaryOperator::Preincrement:
        case UnaryOperator::Predecrement:
        case UnaryOperator::Postincrement:
        case UnaryOperator::Postdecrement:
            // Type is already set via the lvalue.
            break;
    }
    return expr;
}

Expression& BinaryExpression::propagateType(Compilation& compilation, BinaryExpression& expr,
                                            const Type& newType) {
    switch (expr.op) {
        case BinaryOperator::Add:
        case BinaryOperator::Subtract:
        case BinaryOperator::Multiply:
        case BinaryOperator::Divide:
        case BinaryOperator::Mod:
        case BinaryOperator::BinaryAnd:
        case BinaryOperator::BinaryOr:
        case BinaryOperator::BinaryXor:
        case BinaryOperator::BinaryXnor:
            expr.type = &newType;
            contextDetermined(compilation, expr.left_, newType);
            contextDetermined(compilation, expr.right_, newType);
            break;
        case BinaryOperator::Equality:
        case BinaryOperator::Inequality:
        case BinaryOperator::CaseEquality:
        case BinaryOperator::CaseInequality:
        case BinaryOperator::GreaterThanEqual:
        case BinaryOperator::GreaterThan:
        case BinaryOperator::LessThanEqual:
        case BinaryOperator::LessThan:
        case BinaryOperator::WildcardEquality:
        case BinaryOperator::WildcardInequality:
            // Type is already set (always 1 bit) and operands are already folded.
            break;
        case BinaryOperator::LogicalAnd:
        case BinaryOperator::LogicalOr:
        case BinaryOperator::LogicalImplication:
        case BinaryOperator::LogicalEquivalence:
            // Type is already set (always 1 bit).
            selfDetermined(compilation, expr.left_);
            selfDetermined(compilation, expr.right_);
            break;
        case BinaryOperator::LogicalShiftLeft:
        case BinaryOperator::LogicalShiftRight:
        case BinaryOperator::ArithmeticShiftLeft:
        case BinaryOperator::ArithmeticShiftRight:
        case BinaryOperator::Power:
            // Only the left hand side gets propagated; the rhs is self determined.
            expr.type = &newType;
            contextDetermined(compilation, expr.left_, newType);
            selfDetermined(compilation, expr.right_);
            break;
    }
    return expr;
}

Expression& ConditionalExpression::propagateType(Compilation& compilation, ConditionalExpression& expr,
                                                 const Type& newType) {
    // predicate is self determined
    expr.type = &newType;
    selfDetermined(compilation, expr.pred_);
    contextDetermined(compilation, expr.left_, newType);
    contextDetermined(compilation, expr.right_, newType);
    return expr;
}

Expression& AssignmentExpression::propagateType(Compilation&, AssignmentExpression& expr,
                                                const Type&) {
    return expr;
}

Expression& ElementSelectExpression::propagateType(Compilation&, ElementSelectExpression& expr,
                                                   const Type&) {
    return expr;
}

Expression& RangeSelectExpression::propagateType(Compilation&, RangeSelectExpression& expr,
                                                 const Type&) {
    return expr;
}

Expression& ConcatenationExpression::propagateType(Compilation&, ConcatenationExpression& expr,
                                                   const Type&) {
    // All operands are self-determined.
    return expr;
}

Expression& ReplicationExpression::propagateType(Compilation&, ReplicationExpression& expr,
                                                 const Type&) {
    return expr;
}

Expression& CallExpression::propagateType(Compilation&, CallExpression& expr,
                                          const Type&) {
    return expr;
}

Expression& ConversionExpression::propagateType(Compilation& compilation, ConversionExpression& expr,
                                                const Type& newType) {
    // predicate is self determined
    expr.type = &newType;
    selfDetermined(compilation, expr.operand_);
    return expr;
}

}