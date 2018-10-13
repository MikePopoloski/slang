//------------------------------------------------------------------------------
// Expressions_prop.cpp
// Expression type propagation.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/Expressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/symbols/ASTVisitor.h"

namespace slang {

// This visitor handles inserting implicit conversions into an expression tree where necessary.
// SystemVerilog has an additional weird feature where the type of one branch of an expression
// tree can bubble up and then propagate back down a different branch, which is also implemented
// here.
struct Expression::PropagationVisitor {
    HAS_METHOD_TRAIT(propagateType);

    Compilation& compilation;
    const Type& newType;

    PropagationVisitor(Compilation& compilation, const Type& newType) :
        compilation(compilation), newType(newType) {}

    template<typename T>
    Expression& visit(T& expr) {
        if (expr.bad())
            return expr;

        if (newType.isError()) {
            expr.type = &newType;
            return expr;
        }

        // If the new type is equivalent to the old type, there's no need for a conversion.
        // Otherwise if both types are integral or both are real, we have to check if the
        // conversion should be pushed further down the tree. Otherwise we should insert
        // the implicit conversion here.
        bool needConversion = !newType.isEquivalent(*expr.type);
        if constexpr (has_propagateType_v<T, bool, Compilation&, const Type&>) {
            if ((newType.isFloating() && expr.type->isFloating()) ||
                (newType.isIntegral() && expr.type->isIntegral())) {

                if (expr.propagateType(compilation, newType))
                    needConversion = false;
            }
        }

        Expression* result = &expr;
        if (needConversion)
            result = &Expression::implicitConversion(compilation, newType, expr);

        // Try to fold any constant values.
        ASSERT(!result->constant);
        EvalContext context;
        ConstantValue value = result->eval(context);
        if (value)
            result->constant = compilation.createConstant(std::move(value));
        return *result;
    }

    Expression& visitInvalid(Expression& expr) { return expr; }
};

void Expression::contextDetermined(Compilation& compilation, Expression*& expr,
                                   const Type& newType) {
    PropagationVisitor visitor(compilation, newType);
    expr = &expr->visit(visitor);
}

void Expression::selfDetermined(Compilation& compilation, Expression*& expr) {
    ASSERT(expr->type);
    PropagationVisitor visitor(compilation, *expr->type);
    expr = &expr->visit(visitor);
}

Expression& Expression::selfDetermined(Compilation& compilation, const ExpressionSyntax& syntax,
                                       const BindContext& context, bitmask<BindFlags> extraFlags) {
    Expression* expr = &create(compilation, syntax, context, extraFlags);
    selfDetermined(compilation, expr);
    return *expr;
}

bool UnbasedUnsizedIntegerLiteral::propagateType(Compilation&, const Type& newType) {
    bitwidth_t newWidth = newType.getBitWidth();
    ASSERT(newType.isIntegral());
    ASSERT(newWidth);

    type = &newType;
    return true;
}

bool UnaryExpression::propagateType(Compilation& compilation, const Type& newType) {
    switch (op) {
        case UnaryOperator::Plus:
        case UnaryOperator::Minus:
        case UnaryOperator::BitwiseNot:
            type = &newType;
            contextDetermined(compilation, operand_, newType);
            return true;
        case UnaryOperator::BitwiseAnd:
        case UnaryOperator::BitwiseOr:
        case UnaryOperator::BitwiseXor:
        case UnaryOperator::BitwiseNand:
        case UnaryOperator::BitwiseNor:
        case UnaryOperator::BitwiseXnor:
        case UnaryOperator::LogicalNot:
        case UnaryOperator::Preincrement:
        case UnaryOperator::Predecrement:
        case UnaryOperator::Postincrement:
        case UnaryOperator::Postdecrement:
            // Operand is self determined and already folded.
            return false;
    }
    THROW_UNREACHABLE;
}

bool BinaryExpression::propagateType(Compilation& compilation, const Type& newType) {
    switch (op) {
        case BinaryOperator::Add:
        case BinaryOperator::Subtract:
        case BinaryOperator::Multiply:
        case BinaryOperator::Divide:
        case BinaryOperator::Mod:
        case BinaryOperator::BinaryAnd:
        case BinaryOperator::BinaryOr:
        case BinaryOperator::BinaryXor:
        case BinaryOperator::BinaryXnor:
            type = &newType;
            contextDetermined(compilation, left_, newType);
            contextDetermined(compilation, right_, newType);
            return true;
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
        case BinaryOperator::LogicalAnd:
        case BinaryOperator::LogicalOr:
        case BinaryOperator::LogicalImplication:
        case BinaryOperator::LogicalEquivalence:
            // Type is already set (always 1 bit) and operands are already folded.
            return false;
        case BinaryOperator::LogicalShiftLeft:
        case BinaryOperator::LogicalShiftRight:
        case BinaryOperator::ArithmeticShiftLeft:
        case BinaryOperator::ArithmeticShiftRight:
        case BinaryOperator::Power:
            // Only the left hand side gets propagated; the rhs is self determined.
            type = &newType;
            contextDetermined(compilation, left_, newType);
            return true;
    }
    THROW_UNREACHABLE;
}

bool ConditionalExpression::propagateType(Compilation& compilation, const Type& newType) {
    // The predicate is self determined so no need to handle it here.
    type = &newType;
    contextDetermined(compilation, left_, newType);
    contextDetermined(compilation, right_, newType);
    return true;
}

} // namespace slang