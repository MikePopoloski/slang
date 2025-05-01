//------------------------------------------------------------------------------
// ConversionExpression.cpp
// Definitions for conversion expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/expressions/ConversionExpression.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Bitstream.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/expressions/LiteralExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/ParameterSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace {

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

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

// This checks whether the two types are essentially the same struct or union type,
// which is true if they have the same number of fields with the same names and the
// same field types.
bool isSameStructUnion(const Type& left, const Type& right) {
    const Type& lt = left.getCanonicalType();
    const Type& rt = right.getCanonicalType();
    if (lt.kind != rt.kind)
        return false;

    if (lt.kind != SymbolKind::PackedStructType && lt.kind != SymbolKind::PackedUnionType)
        return false;

    auto lr = lt.as<Scope>().membersOfType<FieldSymbol>();
    auto rr = rt.as<Scope>().membersOfType<FieldSymbol>();

    auto lit = lr.begin();
    auto rit = rr.begin();
    while (lit != lr.end()) {
        if (rit == rr.end() || lit->name != rit->name)
            return false;

        auto& lft = lit->getType();
        auto& rft = rit->getType();
        if (!lft.isMatching(rft) && !isSameStructUnion(lft, rft))
            return false;

        ++lit;
        ++rit;
    }
    return rit == rr.end();
}

bool isUnionMemberType(const Type& left, const Type& right) {
    const Type& lt = left.getCanonicalType();
    const Type& rt = right.getCanonicalType();
    if (!lt.isPackedUnion())
        return false;

    for (auto& field : lt.as<Scope>().membersOfType<FieldSymbol>()) {
        auto& ft = field.getType();
        if (ft.isMatching(rt) || isUnionMemberType(ft, rt))
            return true;
    }
    return false;
}

bool hasSameDims(const Type& left, const Type& right) {
    if (left.getFixedRange().width() != right.getFixedRange().width())
        return false;

    auto le = left.getArrayElementType();
    auto re = right.getArrayElementType();
    if (bool(le) != bool(re))
        return false;

    if (!le)
        return true;

    return hasSameDims(*le, *re);
}

} // namespace

namespace slang::ast {

using namespace parsing;
using namespace syntax;

bool Expression::isImplicitlyAssignableTo(Compilation& compilation, const Type& targetType) const {
    if (targetType.isAssignmentCompatible(*type))
        return true;

    // String literals have a type of integer, but are allowed to implicitly convert to the
    // string type.
    if ((targetType.isString() || targetType.isByteArray()) && isImplicitString())
        return true;

    if (targetType.isEnum()) {
        return isSameEnum(*this, targetType) ||
               (type->isIntegral() && compilation.hasFlag(CompilationFlags::RelaxEnumConversions));
    }

    if (type->isString() && targetType.isIntegral() &&
        compilation.hasFlag(CompilationFlags::RelaxStringConversions)) {
        return true;
    }

    return false;
}

Expression& Expression::convertAssignment(const ASTContext& context, const Type& type,
                                          Expression& expr, SourceRange assignmentRange,
                                          Expression** lhsExpr, bitmask<AssignFlags>* assignFlags) {
    if (expr.bad())
        return expr;

    Compilation& comp = context.getCompilation();
    if (type.isError())
        return badExpr(comp, &expr);

    Expression* result = &expr;
    const Type* rt = expr.type;

    auto finalizeType = [&](const Type& t) {
        contextDetermined(context, result, nullptr, t, assignmentRange, ConversionKind::Implicit);
    };

    if (type.isEquivalent(*rt)) {
        finalizeType(*rt);

        if (type.isVoid())
            context.addDiag(diag::VoidAssignment, expr.sourceRange);

        // If the types are not actually matching we might still want
        // to issue conversion warnings.
        if (!context.inUnevaluatedBranch() && !type.isMatching(*rt)) {
            ConversionExpression::checkImplicitConversions(context, *rt, type, *result, nullptr,
                                                           assignmentRange,
                                                           ConversionKind::Implicit);
        }

        return *result;
    }

    // If this is a port connection to an array of instances, check if the provided
    // expression represents an array that should be sliced on a per-instance basis.
    auto instance = context.getInstance();
    if (instance && !instance->arrayPath.empty()) {
        // If the connection is already of the right size and simply differs in
        // terms of four-statedness or signedness, don't bother trying to slice
        // out the connection.
        if (type.getBitWidth() != rt->getBitWidth() || !type.isAssignmentCompatible(*rt)) {
            // If we have an lhsExpr here, this is an output (or inout) port being connected.
            // We need to pass the lhs in as the expression to be connected, since we can't
            // slice the port side. If lhsExpr is null, this is an input port and we should
            // slice the incoming expression as an rvalue.
            if (lhsExpr) {
                Expression* conn = tryConnectPortArray(context, *rt, **lhsExpr, *instance);
                if (conn) {
                    selfDetermined(context, conn);
                    *lhsExpr = conn;

                    SLANG_ASSERT(assignFlags);
                    if (assignFlags)
                        *assignFlags |= AssignFlags::SlicedPort;

                    selfDetermined(context, result);
                    return *result;
                }
            }
            else {
                Expression* conn = tryConnectPortArray(context, type, expr, *instance);
                if (conn) {
                    selfDetermined(context, conn);
                    return *conn;
                }
            }
        }
    }

    if (!type.isAssignmentCompatible(*rt)) {
        if (expr.isImplicitlyAssignableTo(comp, type)) {
            return ConversionExpression::makeImplicit(context, type, ConversionKind::Implicit,
                                                      *result, nullptr, assignmentRange);
        }

        if (expr.kind == ExpressionKind::Streaming) {
            if (Bitstream::canBeSource(type, expr.as<StreamingConcatenationExpression>(),
                                       assignmentRange, context)) {
                // Add an implicit bit-stream casting otherwise types are not assignment compatible.
                // The size rule is not identical to explicit bit-stream casting so a different
                // ConversionKind is used.
                result = comp.emplace<ConversionExpression>(type, ConversionKind::StreamingConcat,
                                                            *result, result->sourceRange);
                selfDetermined(context, result);
                return *result;
            }
            return badExpr(comp, &expr);
        }

        if (expr.kind == ExpressionKind::ValueRange) {
            // Convert each side of the range and return that as a new range.
            auto convert = [&](Expression& expr) -> Expression& {
                if (expr.kind == ExpressionKind::UnboundedLiteral)
                    return expr;
                return convertAssignment(context, type, expr, assignmentRange, lhsExpr,
                                         assignFlags);
            };

            auto& vre = expr.as<ValueRangeExpression>();
            result = comp.emplace<ValueRangeExpression>(*expr.type, vre.rangeKind,
                                                        convert(vre.left()), convert(vre.right()),
                                                        expr.sourceRange);
            result->syntax = expr.syntax;
            return *result;
        }

        DiagCode code = diag::BadAssignment;
        if (!context.flags.has(ASTFlags::OutputArg) &&
            (type.isCastCompatible(*rt) || type.isBitstreamCastable(*rt))) {
            code = diag::NoImplicitConversion;
        }

        auto& diag = context.addDiag(code, assignmentRange);
        diag << *rt << type;
        if (lhsExpr)
            diag << (*lhsExpr)->sourceRange;

        diag << expr.sourceRange;
        return badExpr(comp, &expr);
    }

    if (type.isNumeric() && rt->isNumeric()) {
        // The "signednessFromRt" flag is important here; only the width of the lhs is
        // propagated down to operands, not the sign flag. Once the expression is appropriately
        // sized, the makeImplicit call down below will convert the sign for us.
        rt = OpInfo::binaryType(comp, &type, rt, false, /* signednessFromRt */ true);

        // If the final type is the same type (or equivalent) of the lhs, we know we're
        // performing an expansion of the rhs. The propagation performed by contextDetermined
        // will ensure that the expression has the correct resulting type, so we don't need an
        // additional implicit conversion. What's not obvious here is that simple assignments like:
        //      logic [3:0] a;
        //      logic [8:0] b;
        //      initial b = a;
        // will still result in an appropriate conversion warning because the type propagation
        // visitor will see that we're in an assignment and insert an implicit conversion for us.
        if (type.isEquivalent(*rt)) {
            finalizeType(type);
            return *result;
        }

        // Otherwise use the common type and fall through to get an implicit conversion
        // created for us.
        finalizeType(*rt);
    }

    return ConversionExpression::makeImplicit(context, type, ConversionKind::Implicit, *result,
                                              nullptr, assignmentRange);
}

static bool actuallyNeededCast(const Type& type, const Expression& operand) {
    // Check whether a cast was needed for the given operand to
    // reach the final type. This is true when the operand requires
    // an assignment-like context to determine its result.
    switch (operand.kind) {
        case ExpressionKind::NewArray:
        case ExpressionKind::NewClass:
        case ExpressionKind::NewCovergroup:
        case ExpressionKind::SimpleAssignmentPattern:
        case ExpressionKind::StructuredAssignmentPattern:
        case ExpressionKind::ReplicatedAssignmentPattern:
        case ExpressionKind::TaggedUnion:
            return true;
        case ExpressionKind::Concatenation:
            return operand.type->isUnpackedArray();
        case ExpressionKind::MinTypMax:
            return actuallyNeededCast(type, operand.as<MinTypMaxExpression>().selected());
        case ExpressionKind::ConditionalOp: {
            auto& cond = operand.as<ConditionalExpression>();
            if (!type.isEquivalent(*cond.left().type) || !type.isEquivalent(*cond.right().type))
                return true;
            return actuallyNeededCast(type, cond.left()) || actuallyNeededCast(type, cond.right());
        }
        default:
            return false;
    }
}

Expression& ConversionExpression::fromSyntax(Compilation& comp, const CastExpressionSyntax& syntax,
                                             const ASTContext& context,
                                             const Type* assignmentTarget) {
    auto& targetExpr = bind(*syntax.left, context, ASTFlags::AllowDataType);
    if (targetExpr.bad())
        return badExpr(comp, nullptr);

    auto type = &comp.getErrorType();
    Expression* operand;
    if (targetExpr.kind == ExpressionKind::DataType) {
        type = targetExpr.type;
        if (!type->isSimpleType() && !type->isError() && !type->isString() &&
            syntax.left->kind != SyntaxKind::TypeReference) {
            context.addDiag(diag::BadCastType, targetExpr.sourceRange) << *type;
            return badExpr(comp, nullptr);
        }

        operand = &create(comp, *syntax.right, context, ASTFlags::StreamingAllowed, type);
        if (operand->bad())
            return badExpr(comp, nullptr);
    }
    else {
        auto val = context.evalInteger(targetExpr);
        if (!val || !context.requireGtZero(val, targetExpr.sourceRange))
            return badExpr(comp, nullptr);

        bitwidth_t width = bitwidth_t(*val);
        if (!context.requireValidBitWidth(width, targetExpr.sourceRange))
            return badExpr(comp, nullptr);

        operand = &create(comp, *syntax.right, context, ASTFlags::StreamingAllowed);
        if (operand->bad())
            return badExpr(comp, nullptr);

        if (!operand->type->isIntegral()) {
            auto& diag = context.addDiag(diag::BadIntegerCast, syntax.apostrophe.location());
            diag << *operand->type;
            diag << targetExpr.sourceRange << operand->sourceRange;
            return badExpr(comp, nullptr);
        }

        type = &comp.getType(width, operand->type->getIntegralFlags());
    }

    auto result = [&](ConversionKind cast = ConversionKind::Explicit) {
        return comp.emplace<ConversionExpression>(*type, cast, *operand, syntax.sourceRange());
    };

    if (!type->isCastCompatible(*operand->type)) {
        if (!Bitstream::checkClassAccess(*type, context, targetExpr.sourceRange)) {
            return badExpr(comp, result());
        }

        if (operand->kind == ExpressionKind::Streaming) {
            if (!Bitstream::isBitstreamCast(*type,
                                            operand->as<StreamingConcatenationExpression>())) {
                auto& diag = context.addDiag(diag::BadStreamCast, syntax.apostrophe.location());
                diag << *type;
                diag << targetExpr.sourceRange << operand->sourceRange;
                return badExpr(comp, result());
            }
        }
        else if (!type->isBitstreamCastable(*operand->type)) {
            auto& diag = context.addDiag(diag::BadConversion, syntax.apostrophe.location());
            diag << *operand->type << *type;
            diag << targetExpr.sourceRange << operand->sourceRange;
            return badExpr(comp, result());
        }
        else if (!Bitstream::checkClassAccess(*operand->type, context, operand->sourceRange)) {
            return badExpr(comp, result());
        }

        return *result(ConversionKind::BitstreamCast);
    }

    // We have a useless cast if the type of the operand matches what we're casting to, unless:
    // - We needed the assignment-like context of the cast (like for an unpacked array concat)
    // - We weren't already in an assignment-like context of the correct type
    // - We're casting a genvar (people dislike seeing warnings about genvar operands)
    // - We're casting to a different typedef even if it's a matching underlying type
    auto isGenvar = [&] {
        if (auto sym = operand->getSymbolReference()) {
            return sym->kind == SymbolKind::Genvar || (sym->kind == SymbolKind::Parameter &&
                                                       sym->as<ParameterSymbol>().isFromGenvar());
        }
        return false;
    };

    auto isDifferentTypedef = [&] {
        return (type->isAlias() || operand->type->isAlias()) && type != operand->type;
    };

    if (type->isMatching(*operand->type) && !isGenvar() && !isDifferentTypedef() &&
        ((assignmentTarget && assignmentTarget->isMatching(*type) &&
          operand->kind != ExpressionKind::ConditionalOp) ||
         !actuallyNeededCast(*type, *operand))) {
        context.addDiag(diag::UselessCast, syntax.apostrophe.location())
            << *operand->type << targetExpr.sourceRange << operand->sourceRange;
    }

    if (type->isAssignmentCompatible(*operand->type)) {
        // The type we propagate should use the sign of the operand, just like it
        // would if we were doing an implicit conversion via an assignment expression.
        auto propagatedType = type;
        if (type->isNumeric() && operand->type->isNumeric()) {
            propagatedType = OpInfo::binaryType(comp, type, operand->type, false,
                                                /* signednessFromRt */ true);
        }

        contextDetermined(context, operand, nullptr, *propagatedType, syntax.apostrophe.range(),
                          ConversionKind::Explicit);

        if (operand->kind == ExpressionKind::Conversion &&
            !operand->as<ConversionExpression>().isImplicit()) {
            operand->sourceRange = syntax.sourceRange();
            operand->type = type;
            return *operand;
        }
    }
    else {
        selfDetermined(context, operand);
    }

    return *result();
}

Expression& ConversionExpression::fromSyntax(Compilation& compilation,
                                             const SignedCastExpressionSyntax& syntax,
                                             const ASTContext& context) {
    auto& operand = selfDetermined(compilation, *syntax.inner, context);
    auto result = compilation.emplace<ConversionExpression>(compilation.getErrorType(),
                                                            ConversionKind::Explicit, operand,
                                                            syntax.sourceRange());
    if (operand.bad())
        return badExpr(compilation, result);

    // SignedCastExpression can also represent a const cast, which does nothing
    // and passes the type through unchanged.
    if (syntax.signing.kind == TokenKind::ConstKeyword) {
        result->type = operand.type;
        return *result;
    }

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

Expression& ConversionExpression::makeImplicit(const ASTContext& context, const Type& targetType,
                                               ConversionKind conversionKind, Expression& expr,
                                               const Expression* parentExpr,
                                               SourceRange operatorRange) {
    auto& comp = context.getCompilation();
    SLANG_ASSERT(expr.isImplicitlyAssignableTo(comp, targetType));

    Expression* op = &expr;
    selfDetermined(context, op);

    auto result = comp.emplace<ConversionExpression>(targetType, conversionKind, *op,
                                                     op->sourceRange);
    result->implicitOpRange = operatorRange;

    if ((conversionKind == ConversionKind::Implicit ||
         conversionKind == ConversionKind::Propagated) &&
        !context.inUnevaluatedBranch()) {
        checkImplicitConversions(context, *op->type, targetType, *result, parentExpr, operatorRange,
                                 conversionKind);
    }

    return *result;
}

ConstantValue ConversionExpression::evalImpl(EvalContext& context) const {
    return applyTo(context, operand().eval(context));
}

ConstantValue ConversionExpression::applyTo(EvalContext& context, ConstantValue&& value) const {
    return convert(context, *operand().type, *type, sourceRange, std::move(value), conversionKind,
                   &operand(), implicitOpRange);
}

ConstantValue ConversionExpression::convert(EvalContext& context, const Type& from, const Type& to,
                                            SourceRange sourceRange, ConstantValue&& value,
                                            ConversionKind conversionKind, const Expression* expr,
                                            SourceRange operatorRange) {
    if (!value)
        return nullptr;

    if (from.isMatching(to))
        return std::move(value);

    if (conversionKind == ConversionKind::BitstreamCast ||
        conversionKind == ConversionKind::StreamingConcat) {
        return Bitstream::evaluateCast(to, std::move(value), sourceRange, context,
                                       conversionKind == ConversionKind::StreamingConcat);
    }

    const bool checkImplicit = conversionKind == ConversionKind::Implicit &&
                               !context.astCtx.flags.has(ASTFlags::UnevaluatedBranch);

    auto addDiag = [&](DiagCode code) -> Diagnostic& {
        if (operatorRange.start())
            return context.addDiag(code, operatorRange) << sourceRange;
        else
            return context.addDiag(code, sourceRange);
    };

    if (to.isIntegral()) {
        // [11.8.2] last bullet says: the operand shall be sign-extended only if the propagated type
        // is signed. It is different from [11.8.3] ConstantValue::convertToInt uses.
        // ConversionKind::Propagated marked in Expression::PropagationVisitor
        if (conversionKind == ConversionKind::Propagated && value.isInteger())
            value.integer().setSigned(to.isSigned());

        auto result = value.convertToInt(to.getBitWidth(), to.isSigned(), to.isFourState());
        if (checkImplicit) {
            if (value.isInteger()) {
                auto& oldInt = value.integer();
                auto& newInt = result.integer();
                if (!oldInt.hasUnknown() && !newInt.hasUnknown() && oldInt != newInt) {
                    if (oldInt.getBitWidth() != newInt.getBitWidth()) {
                        addDiag(diag::ConstantConversion) << from << to << oldInt << newInt;
                    }
                    else {
                        SLANG_ASSERT(oldInt.isSigned() != newInt.isSigned());
                        if (!expr ||
                            !signMatches(expr->getEffectiveSign(/* isForConversion */ true),
                                         EffectiveSign::Signed)) {
                            addDiag(diag::SignConversion) << from << to;
                        }
                    }
                }
            }
            else if (value.isReal() || value.isShortReal()) {
                const bool differs = value.isReal()
                                         ? value.real() != result.integer().toDouble()
                                         : value.shortReal() != result.integer().toFloat();
                if (differs)
                    addDiag(diag::ConstantConversion) << from << to << value << result;
            }
        }

        return result;
    }

    if (to.isFloating()) {
        auto result = to.getBitWidth() == 32 ? value.convertToShortReal() : value.convertToReal();
        if (checkImplicit && value.isInteger()) {
            const bool differs = result.isReal()
                                     ? (int64_t)result.real() != value.integer().as<int64_t>()
                                     : (int32_t)result.shortReal() != value.integer().as<int32_t>();
            if (differs)
                addDiag(diag::ConstantConversion) << from << to << value << result;
        }
        return result;
    }

    if (to.isString())
        return value.convertToStr();

    if (to.isUnpackedArray() && from.isUnpackedArray()) {
        // Conversion to a dynamic array just resizes. Conversion to a fixed array
        // must have the same number of elements in the source.
        SLANG_ASSERT(!to.hasFixedRange() || !from.hasFixedRange());
        if (to.hasFixedRange()) {
            size_t size = value.size();
            if (size != to.getFixedRange().width()) {
                addDiag(diag::ConstEvalDynamicToFixedSize) << from << size << to;
                return nullptr;
            }
        }

        if (!to.isQueue() && from.isQueue()) {
            // Convert from queue to vector.
            auto& q = *value.queue();
            return std::vector(q.begin(), q.end());
        }

        if (to.isQueue() && !from.isQueue()) {
            // Convert from vector to queue.
            auto elems = value.elements();
            SVQueue result(elems.begin(), elems.end());
            result.maxBound = to.getCanonicalType().as<QueueType>().maxBound;
            result.resizeToBound();
            return result;
        }

        return std::move(value);
    }

    if (to.isByteArray()) {
        auto& ct = to.getCanonicalType();
        bool isSigned = ct.getArrayElementType()->isSigned();
        if (ct.isQueue())
            return value.convertToByteQueue(isSigned);

        bitwidth_t size;
        if (ct.hasFixedRange())
            size = ct.as<FixedSizeUnpackedArrayType>().range.width();
        else
            size = 0; // dynamic array use string size

        return value.convertToByteArray(size, isSigned);
    }

    // Null can be assigned to various destination types. It's ok to just
    // keep propagating the null value.
    if (from.isNull())
        return std::move(value);

    SLANG_UNREACHABLE;
}

void ConversionExpression::checkImplicitConversions(
    const ASTContext& context, const Type& sourceType, const Type& targetType, const Expression& op,
    const Expression* parentExpr, SourceRange operatorRange, ConversionKind conversionKind) {

    auto isStructUnionEnum = [](const Type& t) {
        return t.kind == SymbolKind::PackedStructType || t.kind == SymbolKind::PackedUnionType ||
               t.kind == SymbolKind::EnumType;
    };

    auto isMultiDimArray = [](const Type& t) {
        return t.kind == SymbolKind::PackedArrayType && t.getArrayElementType()->getBitWidth() > 1;
    };

    auto parentIsComparison = [&] {
        return parentExpr && parentExpr->kind == ExpressionKind::BinaryOp &&
               OpInfo::isComparison(parentExpr->as<BinaryExpression>().op);
    };

    auto addDiag = [&](DiagCode code) -> Diagnostic& {
        auto& diag = context.addDiag(code, op.sourceRange);
        if (operatorRange.start())
            diag << operatorRange;
        return diag;
    };

    // Don't warn about conversions in compound assignment operators.
    auto isCompoundAssign = [&] {
        auto& expr = op.unwrapImplicitConversions();
        if (expr.kind == ExpressionKind::LValueReference)
            return true;

        return expr.kind == ExpressionKind::BinaryOp &&
               expr.as<BinaryExpression>().left().unwrapImplicitConversions().kind ==
                   ExpressionKind::LValueReference;
    };
    if (isCompoundAssign())
        return;

    const Type& lt = targetType.getCanonicalType();
    const Type& rt = sourceType.getCanonicalType();
    if (lt.isIntegral() && rt.isIntegral()) {
        // Warn for conversions between different enums/structs/unions.
        if (isStructUnionEnum(lt) && isStructUnionEnum(rt) && !lt.isMatching(rt)) {
            if (!isSameStructUnion(lt, rt) && !isUnionMemberType(lt, rt))
                addDiag(diag::ImplicitConvert) << sourceType << targetType;
            return;
        }

        // Warn for conversions between packed arrays of differing
        // dimension counts or sizes.
        if (isMultiDimArray(lt) && isMultiDimArray(rt) && !hasSameDims(lt, rt)) {
            // Avoid warning for assignments or comparisons with 0 or '0, '1.
            auto isZeroOrUnsized = [](const Expression& e) {
                auto expr = &e.unwrapImplicitConversions();
                if (expr->kind == ExpressionKind::ConditionalOp) {
                    if (auto known = expr->as<ConditionalExpression>().knownSide())
                        expr = known;
                }

                return expr->kind == ExpressionKind::UnbasedUnsizedIntegerLiteral ||
                       (expr->kind == ExpressionKind::IntegerLiteral &&
                        bool(expr->as<IntegerLiteral>().getValue() == 0));
            };

            if (!isZeroOrUnsized(op) &&
                (!parentIsComparison() ||
                 !isZeroOrUnsized(parentExpr->as<BinaryExpression>().right()))) {
                addDiag(diag::PackedArrayConv) << sourceType << targetType;
            }
        }

        // Check to rule out false positives: try to eval as a constant.
        // We'll ignore any constants, because they will get their own more
        // fine grained warning during eval.
        if (context.tryEval(op))
            return;

        // Warn for sign conversions.
        if (lt.isSigned() != rt.isSigned()) {
            // Comparisons get their own warning elsewhere.
            if (!parentIsComparison() && op.getEffectiveSign(/* isForConversion */ false) !=
                                             Expression::EffectiveSign::Either) {
                addDiag(diag::SignConversion) << sourceType << targetType;
            }
        }

        // Don't issue width warnings for propagated conversions, as they would
        // be extremely noisy and of dubious value (since they act the way people
        // expect their expressions to behave).
        if (conversionKind == ConversionKind::Propagated)
            return;

        // Warn for implicit assignments between integral types of differing widths.
        bitwidth_t targetWidth = lt.getBitWidth();
        bitwidth_t actualWidth = rt.getBitWidth();
        if (targetWidth == actualWidth)
            return;

        // Before we go and issue this warning, weed out false positives by
        // recomputing the width of the expression, with all constants sized
        // to the minimum width necessary to represent them. Otherwise, even
        // code as simple as this will result in a warning:
        //    logic [3:0] a = 1;
        std::optional<bitwidth_t> effective = op.getEffectiveWidth();
        if (!effective)
            return;

        // Now that we know the effective width, compare it to the expression's
        // actual width. We don't warn if the target is anywhere in between the
        // effective and the actual width.
        SLANG_ASSERT(effective <= actualWidth);
        if (targetWidth < effective || targetWidth > actualWidth) {
            DiagCode code;
            if (context.getInstance())
                code = targetWidth < effective ? diag::PortWidthTruncate : diag::PortWidthExpand;
            else
                code = targetWidth < effective ? diag::WidthTruncate : diag::WidthExpand;
            addDiag(code) << actualWidth << targetWidth;
        }
    }
    else if (lt.isNumeric() && rt.isNumeric()) {
        // Don't warn for constexprs.
        if (context.tryEval(op))
            return;

        DiagCode code;
        if (lt.isIntegral())
            code = diag::FloatIntConv;
        else if (rt.isIntegral())
            code = diag::IntFloatConv;
        else if (lt.getBitWidth() < rt.getBitWidth())
            code = diag::FloatNarrow;
        else if (lt.getBitWidth() > rt.getBitWidth())
            code = diag::FloatWiden;
        else
            return;

        addDiag(code) << sourceType << targetType;
    }
}

std::optional<bitwidth_t> ConversionExpression::getEffectiveWidthImpl() const {
    if (isImplicit())
        return operand().getEffectiveWidth();
    return type->getBitWidth();
}

Expression::EffectiveSign ConversionExpression::getEffectiveSignImpl(bool isForConversion) const {
    if (isImplicit())
        return operand().getEffectiveSign(isForConversion);
    return type->isSigned() ? EffectiveSign::Signed : EffectiveSign::Unsigned;
}

void ConversionExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("operand", operand());
}

} // namespace slang::ast
