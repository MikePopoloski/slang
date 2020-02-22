//------------------------------------------------------------------------------
// AssignmentExpressions.cpp
// Definitions for assignment-related expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/AssignmentExpressions.h"

#include "slang/binding/LiteralExpressions.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/binding/OperatorExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/AllTypes.h"
#include "slang/symbols/DefinitionSymbols.h"
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

Expression* Expression::tryConnectPortArray(const BindContext& context, const Type& type,
                                            Expression& expr, const InstanceSymbol& instance) {
    auto& comp = context.getCompilation();
    auto& ct = expr.type->getCanonicalType();
    if (ct.kind == SymbolKind::UnpackedArrayType) {
        SmallVectorSized<ConstantRange, 8> connDims;
        const Type* elemType = ct.getFullArrayBounds(connDims);
        ASSERT(elemType);

        SmallVectorSized<ConstantRange, 8> instanceDims;
        instance.getArrayDimensions(instanceDims);

        // If we don't have enough connections dims to satisfy all of the
        // instance dims, give up now.
        if (connDims.size() < instanceDims.size())
            return nullptr;

        span<const ConstantRange> extraDims = connDims;
        extraDims = extraDims.subspan(instanceDims.size());
        if (!extraDims.empty())
            elemType = &UnpackedArrayType::fromDims(comp, *elemType, extraDims);

        // Element types must be equivalent and all array dimension sizes must match
        bool bad = false;
        if (!type.isEquivalent(*elemType)) {
            bad = true;
        }
        else {
            for (size_t i = 0; i < instanceDims.size(); i++) {
                if (connDims[i].width() != instanceDims[i].width()) {
                    bad = true;
                    break;
                }
            }
        }

        if (bad) {
            auto& diag = context.addDiag(diag::PortConnArrayMismatch, expr.sourceRange);
            diag << *expr.type << type;

            string_view name = instance.getArrayName();
            if (name.empty())
                diag << "<unknown>"sv;
            else {
                diag << name;
                if (instance.location)
                    diag << SourceRange{ instance.location, instance.location + name.length() };
            }

            return &badExpr(comp, &expr);
        }

        // Select each element of the connection array based on the index of
        // the instance in the instance array path. Elements get matched
        // left index to left index.
        Expression* result = &expr;
        for (size_t i = 0; i < instance.arrayPath.size(); i++) {
            // First translate the path index since it's relative to that particular
            // array's declared range.
            int32_t index = instanceDims[i].translateIndex(instance.arrayPath[i]);

            // Now translate back to be relative to the connection type's declared range.
            if (!connDims[i].isLittleEndian())
                index = connDims[i].upper() - index;
            else
                index = connDims[i].lower() + index;

            result = &ElementSelectExpression::fromConstant(comp, *result, index, context);
            if (result->bad())
                break;
        }

        return result;
    }

    return nullptr;
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

        // If this is a port connection to an array of instances, check if the provided
        // expression represents an array that should be sliced on a per-instance basis.
        if (context.instance && !context.instance->arrayPath.empty()) {
            Expression* result = tryConnectPortArray(context, type, expr, *context.instance);
            if (result) {
                selfDetermined(context, result);
                return *result;
            }
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

    // If this is an enum initializer and we just discard unknown bits by
    // implicitly converting to a 2-state result, the standard says we
    // should declare this an error.
    if ((context.flags & BindFlags::EnumInitializer) != 0 && !type.isFourState() && expr.constant &&
        expr.constant->isInteger() && expr.constant->integer().hasUnknown()) {
        context.addDiag(diag::EnumValueUnknownBits, expr.sourceRange) << *expr.constant << type;
        return badExpr(compilation, result);
    }

    return *result;
}

Expression& AssignmentExpression::fromSyntax(Compilation& compilation,
                                             const BinaryExpressionSyntax& syntax,
                                             const BindContext& context) {
    if ((context.flags & BindFlags::AssignmentAllowed) == 0) {
        if (context.flags & BindFlags::ProceduralStatement)
            context.addDiag(diag::AssignmentRequiresParens, syntax.sourceRange());
        else
            context.addDiag(diag::AssignmentNotAllowed, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

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

            return fromComponents(compilation, op, isNonBlocking, *lhs, *rhs,
                                  syntax.operatorToken.location(), syntax.sourceRange(), context);
        }
    }

    Expression& lhs = selfDetermined(compilation, *syntax.left, context);
    Expression& rhs = create(compilation, *syntax.right, context, BindFlags::None, lhs.type);

    return fromComponents(compilation, op, isNonBlocking, lhs, rhs, syntax.operatorToken.location(),
                          syntax.sourceRange(), context);
}

Expression& AssignmentExpression::fromComponents(Compilation& compilation,
                                                 optional<BinaryOperator> op, bool nonBlocking,
                                                 Expression& lhs, Expression& rhs,
                                                 SourceLocation assignLoc, SourceRange sourceRange,
                                                 const BindContext& context) {
    auto result = compilation.emplace<AssignmentExpression>(op, nonBlocking, *lhs.type, lhs, rhs,
                                                            sourceRange);
    if (lhs.bad() || rhs.bad())
        return badExpr(compilation, result);

    // Make sure we can actually assign to the thing on the lhs.
    // TODO: check for const assignment
    if (!context.requireLValue(lhs, assignLoc))
        return badExpr(compilation, result);

    result->right_ =
        &convertAssignment(context, *lhs.type, *result->right_, assignLoc, lhs.sourceRange);
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

void AssignmentExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("left", left());
    serializer.write("right", right());
    serializer.write("isNonBlocking", isNonBlocking());
    if (op)
        serializer.write("op", toString(*op));
}

Expression& ConversionExpression::fromSyntax(Compilation& compilation,
                                             const CastExpressionSyntax& syntax,
                                             const BindContext& context) {
    auto& targetExpr = bind(*syntax.left, context, BindFlags::AllowDataType | BindFlags::Constant);
    auto& operand = selfDetermined(compilation, *syntax.right, context);

    auto result = compilation.emplace<ConversionExpression>(compilation.getErrorType(), false,
                                                            operand, syntax.sourceRange());
    if (targetExpr.bad() || operand.bad())
        return badExpr(compilation, result);

    if (targetExpr.kind == ExpressionKind::DataType) {
        result->type = targetExpr.type;
        if (!result->type->isSimpleType() && !result->type->isError() &&
            !result->type->isString()) {
            context.addDiag(diag::BadCastType, targetExpr.sourceRange) << *result->type;
            return badExpr(compilation, result);
        }
    }
    else {
        auto val = context.evalInteger(targetExpr);
        if (!val || !context.requireGtZero(val, targetExpr.sourceRange))
            return badExpr(compilation, result);

        bitwidth_t width = bitwidth_t(*val);
        if (!context.requireValidBitWidth(width, targetExpr.sourceRange))
            return badExpr(compilation, result);

        if (!operand.type->isIntegral()) {
            auto& diag = context.addDiag(diag::BadIntegerCast, syntax.apostrophe.location());
            diag << *operand.type;
            diag << targetExpr.sourceRange << operand.sourceRange;
            return badExpr(compilation, result);
        }

        result->type = &compilation.getType(width, operand.type->getIntegralFlags());
    }

    const Type& type = *result->type;
    if (!type.isCastCompatible(*operand.type)) {
        auto& diag = context.addDiag(diag::BadConversion, syntax.apostrophe.location());
        diag << *operand.type << type;
        diag << targetExpr.sourceRange << operand.sourceRange;
        return badExpr(compilation, result);
    }

    return *result;
}

Expression& ConversionExpression::fromSyntax(Compilation& compilation,
                                             const SignedCastExpressionSyntax& syntax,
                                             const BindContext& context) {
    auto& operand = selfDetermined(compilation, *syntax.inner, context);
    auto result = compilation.emplace<ConversionExpression>(compilation.getErrorType(), false,
                                                            operand, syntax.sourceRange());
    if (operand.bad())
        return badExpr(compilation, result);

    if (!operand.type->isIntegral()) {
        auto& diag = context.addDiag(diag::BadIntegerCast, syntax.apostrophe.location());
        diag << *operand.type;
        diag << operand.sourceRange;
        return badExpr(compilation, result);
    }

    auto flags = operand.type->getIntegralFlags() & ~IntegralFlags::Signed;
    if (syntax.signing.kind == TokenKind::SignedKeyword)
        flags |= IntegralFlags::Signed;

    result->type = &compilation.getType(operand.type->getBitWidth(), flags);
    return *result;
}

ConstantValue ConversionExpression::evalImpl(EvalContext& context) const {
    ConstantValue value = operand().eval(context);

    const Type& to = *type;
    if (to.isIntegral())
        return value.convertToInt(to.getBitWidth(), to.isSigned(), to.isFourState());

    if (to.isFloating()) {
        switch (to.getBitWidth()) {
            case 32:
                return value.convertToShortReal();
            case 64:
                return value.convertToReal();
            default:
                THROW_UNREACHABLE;
        }
    }

    if (to.isString())
        return value.convertToStr();

    // TODO: other types
    THROW_UNREACHABLE;
}

bool ConversionExpression::verifyConstantImpl(EvalContext& context) const {
    return operand().verifyConstant(context);
}

void ConversionExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("operand", operand());
}

} // namespace slang