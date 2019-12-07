//------------------------------------------------------------------------------
// AssignmentExpressions.cpp
// Definitions for assignment-related expressions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/AssignmentExpressions.h"

#include <nlohmann/json.hpp>

#include "slang/binding/LiteralExpressions.h"
#include "slang/binding/OperatorExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/symbols/Type.h"
#include "slang/syntax/AllSyntax.h"

namespace {

using namespace slang;

bool recurseCheckEnum(const Expression& expr) {
    switch (expr.kind) {
        case ExpressionKind::UnbasedUnsizedIntegerLiteral:
        case ExpressionKind::NamedValue:
        case ExpressionKind::MemberAccess:
            return true;
        case ExpressionKind::IntegerLiteral:
            return expr.as<IntegerLiteral>().isDeclaredUnsized;
        case ExpressionKind::UnaryOp:
            return recurseCheckEnum(expr.as<UnaryExpression>().operand());
        case ExpressionKind::BinaryOp: {
            auto& bin = expr.as<BinaryExpression>();
            return recurseCheckEnum(bin.left()) && recurseCheckEnum(bin.right());
        }
        case ExpressionKind::ConditionalOp: {
            auto& cond = expr.as<ConditionalExpression>();
            return recurseCheckEnum(cond.left()) && recurseCheckEnum(cond.right());
        }
        case ExpressionKind::Conversion: {
            auto& conv = expr.as<ConversionExpression>();
            return conv.isImplicit && recurseCheckEnum(conv.operand());
        }
        default:
            return false;
    }
}

bool checkEnumInitializer(const BindContext& context, const Type& lt, const Expression& rhs) {
    // [6.19] says that the initializer for an enum value must be an integer expression that
    // does not truncate any bits. Furthermore, if a sized literal constant is used, it must
    // be sized exactly to the size of the enum base type. It's not well defined what happens
    // if the sized constant is used further down in some sub-expression, so what we check here
    // is cases where it seems ok to suppress the error:
    // - Unsized literals, variable references
    // - Unary, binary, conditional expressions of the above

    const Type& rt = *rhs.type;
    if (!rt.isIntegral()) {
        context.addDiag(diag::ValueMustBeIntegral, rhs.sourceRange);
        return false;
    }

    if (lt.getBitWidth() == rt.getBitWidth())
        return true;

    if (!recurseCheckEnum(rhs)) {
        auto& diag = context.addDiag(diag::EnumValueSizeMismatch, rhs.sourceRange);
        diag << rt.getBitWidth() << lt.getBitWidth();
        return false;
    }

    return true;
}

// This function exists to handle a case like:
//      integer i;
//      enum { A, B } foo;
//      initial foo = i ? A : B;
// This would otherwise be disallowed because using a 4-state predicate
// means the result of the conditional operator would be 4-state, and
// the enum base type is not 4-state.
bool isSameEnum(const Expression& expr, const Type& enumType) {
    if (expr.kind == ExpressionKind::ConditionalOp) {
        auto& cond = expr.as<ConditionalExpression>();
        return isSameEnum(cond.left(), enumType) && isSameEnum(cond.right(), enumType);
    }
    return expr.type->isMatching(enumType);
}

} // namespace

namespace slang {

Expression& Expression::implicitConversion(const BindContext& context, const Type& targetType,
                                           Expression& expr) {
    ASSERT(targetType.isAssignmentCompatible(*expr.type) ||
           (targetType.isString() && expr.isImplicitString()) ||
           (targetType.isEnum() && isSameEnum(expr, targetType)));
    ASSERT(!targetType.isEquivalent(*expr.type));

    Expression* result = &expr;
    selfDetermined(context, result);
    return *context.scope.getCompilation().emplace<ConversionExpression>(targetType, true, *result,
                                                                         result->sourceRange);
}

Expression& Expression::convertAssignment(const BindContext& context, const Type& type,
                                          Expression& expr, SourceLocation location,
                                          optional<SourceRange> lhsRange) {
    if (expr.bad())
        return expr;

    Compilation& compilation = context.scope.getCompilation();
    if (type.isError())
        return badExpr(compilation, &expr);

    const Type* rt = expr.type;
    if (!type.isAssignmentCompatible(*rt)) {
        // String literals have a type of integer, but are allowed to implicitly convert to the
        // string type. See comments on isSameEnum for why that's here as well.
        if ((type.isString() && expr.isImplicitString()) ||
            (type.isEnum() && isSameEnum(expr, type))) {

            Expression* result = &expr;
            result = &implicitConversion(context, type, *result);
            selfDetermined(context, result);
            return *result;
        }

        DiagCode code =
            type.isCastCompatible(*rt) ? diag::NoImplicitConversion : diag::BadAssignment;
        auto& diag = context.addDiag(code, location);
        diag << *rt << type;
        if (lhsRange)
            diag << *lhsRange;

        diag << expr.sourceRange;
        return badExpr(compilation, &expr);
    }

    Expression* result = &expr;
    if (type.isEquivalent(*rt)) {
        selfDetermined(context, result);
        return *result;
    }

    if (type.isNumeric() && rt->isNumeric()) {
        if ((context.flags & BindFlags::EnumInitializer) != 0 &&
            !checkEnumInitializer(context, type, *result)) {

            return badExpr(compilation, &expr);
        }

        rt = binaryOperatorType(compilation, &type, rt, false);
        contextDetermined(context, result, *rt);

        if (type.isEquivalent(*rt))
            return *result;

        result =
            compilation.emplace<ConversionExpression>(type, true, *result, result->sourceRange);
    }
    else {
        result = &implicitConversion(context, type, *result);
    }

    selfDetermined(context, result);
    return *result;
}

Expression& AssignmentExpression::fromSyntax(Compilation& compilation,
                                             const BinaryExpressionSyntax& syntax,
                                             const BindContext& context) {
    // TODO: verify that assignment is allowed in this expression context
    optional<BinaryOperator> op;
    if (syntax.kind != SyntaxKind::AssignmentExpression &&
        syntax.kind != SyntaxKind::NonblockingAssignmentExpression) {
        op = getBinaryOperator(syntax.kind);
    }

    bool isNonBlocking = syntax.kind == SyntaxKind::NonblockingAssignmentExpression;

    // The right hand side of an assignment expression is typically an
    // "assignment-like context", except if the left hand side does not
    // have a self-determined type. That can only be true if the lhs is
    // an assignment pattern without an explicit type.
    if (syntax.left->kind == SyntaxKind::AssignmentPatternExpression) {
        auto& pattern = syntax.left->as<AssignmentPatternExpressionSyntax>();
        if (!pattern.type) {
            // In this case we have to bind the rhs first to determine the
            // correct type to use as the context for the lhs.
            Expression* rhs = &selfDetermined(compilation, *syntax.right, context);
            if (rhs->bad())
                return badExpr(compilation, rhs);

            Expression* lhs =
                &create(compilation, *syntax.left, context, BindFlags::None, rhs->type);
            selfDetermined(context, lhs);

            auto result = compilation.emplace<AssignmentExpression>(
                op, isNonBlocking, *lhs->type, *lhs, *rhs, syntax.sourceRange());

            if (rhs->bad())
                return badExpr(compilation, result);

            return *result;
        }
    }

    Expression& lhs = selfDetermined(compilation, *syntax.left, context);
    Expression& rhs = create(compilation, *syntax.right, context, BindFlags::None, lhs.type);

    auto result = compilation.emplace<AssignmentExpression>(op, isNonBlocking, *lhs.type, lhs, rhs,
                                                            syntax.sourceRange());
    if (lhs.bad() || rhs.bad())
        return badExpr(compilation, result);

    // Make sure we can actually assign to the thing on the lhs.
    // TODO: check for const assignment
    auto location = syntax.operatorToken.location();
    if (!context.requireLValue(lhs, location))
        return badExpr(compilation, result);

    result->right_ =
        &convertAssignment(context, *lhs.type, *result->right_, location, lhs.sourceRange);
    if (result->right_->bad())
        return badExpr(compilation, result);

    return *result;
}

ConstantValue AssignmentExpression::evalImpl(EvalContext& context) const {
    LValue lvalue = left().evalLValue(context);
    ConstantValue rvalue = right().eval(context);
    if (!lvalue || !rvalue)
        return nullptr;

    if (isCompound())
        rvalue = evalBinaryOperator(*op, lvalue.load(), rvalue);

    lvalue.store(rvalue);
    return rvalue;
}

bool AssignmentExpression::verifyConstantImpl(EvalContext& context) const {
    return left().verifyConstant(context) && right().verifyConstant(context);
}

void AssignmentExpression::toJson(json& j) const {
    j["left"] = left();
    j["right"] = right();
    j["isNonBlocking"] = isNonBlocking();
    if (op)
        j["op"] = toString(*op);
}

} // namespace slang