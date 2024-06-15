//------------------------------------------------------------------------------
// AssignmentExpressions.cpp
// Definitions for assignment-related expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/expressions/AssignmentExpressions.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Bitstream.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/ast/expressions/LiteralExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/CoverSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/numeric/MathUtils.h"
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

void checkImplicitConversions(const ASTContext& context, const Type& sourceType,
                              const Type& targetType, const Expression& op,
                              const Expression* parentExpr, SourceRange operatorRange,
                              ConversionKind conversionKind) {
    auto isStructUnionEnum = [](const Type& t) {
        return t.kind == SymbolKind::PackedStructType || t.kind == SymbolKind::PackedUnionType ||
               t.kind == SymbolKind::EnumType;
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

        // Check to rule out false positives: try to eval as a constant.
        // We'll ignore any constants, because they will get their own more
        // fine grained warning during eval.
        if (context.tryEval(op))
            return;

        // Warn for sign conversions.
        if (lt.isSigned() != rt.isSigned()) {
            // Comparisons get their own warning elsewhere.
            bool isComparison = false;
            if (parentExpr && parentExpr->kind == ExpressionKind::BinaryOp) {
                switch (parentExpr->as<BinaryExpression>().op) {
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
                        isComparison = true;
                        break;
                    default:
                        break;
                }
            }

            if (!isComparison)
                addDiag(diag::SignConversion) << sourceType << targetType;
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

} // namespace

namespace slang::ast {

using namespace parsing;
using namespace syntax;

Expression* Expression::tryConnectPortArray(const ASTContext& context, const Type& portType,
                                            Expression& expr, const InstanceSymbolBase& instance) {
    // This lambda is shared code for reporting an error and returning an invalid expression.
    auto& comp = context.getCompilation();
    auto bad = [&]() {
        auto& diag = context.addDiag(diag::PortConnArrayMismatch, expr.sourceRange);
        diag << *expr.type << portType;

        std::string_view name = instance.getArrayName();
        if (name.empty())
            diag << "<unknown>"sv;
        else {
            diag << name;
            if (instance.location)
                diag << SourceRange{instance.location, instance.location + name.length()};
        }

        return &badExpr(comp, &expr);
    };

    // Collect all of the dimensions of the instance array that owns the provided instance, ex:
    // MyMod instArray [3][4] (.conn(vec));
    //                 ^~~~~~  // these guys
    SmallVector<ConstantRange> instanceDimVec;
    instance.getArrayDimensions(instanceDimVec);

    std::span<const ConstantRange> instanceDims = instanceDimVec;
    std::span<const int32_t> arrayPath = instance.arrayPath;

    // If the connection has any unpacked dimensions, match them up with
    // the leading instance dimensions now.
    Expression* result = &expr;
    const Type* ct = &expr.type->getCanonicalType();
    if (ct->kind == SymbolKind::FixedSizeUnpackedArrayType) {
        SmallVector<ConstantRange> unpackedDimVec;
        const FixedSizeUnpackedArrayType* curr = &ct->as<FixedSizeUnpackedArrayType>();
        while (true) {
            unpackedDimVec.push_back(curr->range);
            ct = &curr->elementType.getCanonicalType();
            if (ct->kind != SymbolKind::FixedSizeUnpackedArrayType)
                break;

            curr = &ct->as<FixedSizeUnpackedArrayType>();
        }

        // Select each element of the connection array based on the index of
        // the instance in the instance array path. Elements get matched
        // left index to left index.
        std::span<const ConstantRange> unpackedDims = unpackedDimVec;
        size_t common = std::min(instanceDims.size(), unpackedDims.size());
        for (size_t i = 0; i < common; i++) {
            if (unpackedDims[i].width() != instanceDims[i].width())
                return bad();

            // To select the right element, translate the path index since it's
            // relative to that particular array's declared range.
            int32_t index = instanceDims[i].translateIndex(arrayPath[i]);

            // Now translate back to be relative to the connection type's declared range.
            if (!unpackedDims[i].isLittleEndian())
                index = unpackedDims[i].upper() - index;
            else
                index = unpackedDims[i].lower() + index;

            result = &ElementSelectExpression::fromConstant(comp, *result, index, context);
            if (result->bad())
                return result; // probably unreachable
        }

        unpackedDims = unpackedDims.subspan(common);
        instanceDims = instanceDims.subspan(common);
        arrayPath = arrayPath.subspan(common);

        // If there are still unpacked dims left, we will have consumed
        // all of the instance dims and whatever is left should match
        // the actual port type to connect.
        if (!unpackedDims.empty()) {
            auto& unpackedType = FixedSizeUnpackedArrayType::fromDims(*context.scope, *ct,
                                                                      unpackedDims,
                                                                      expr.sourceRange);
            if (!portType.isEquivalent(unpackedType)) {
                return bad();
            }

            SLANG_ASSERT(instanceDims.empty());
            SLANG_ASSERT(arrayPath.empty());
            return result;
        }

        // If there are no instance dims left, just make sure the remaining type matches
        // the port and we're good to go.
        if (instanceDims.empty())
            return portType.isEquivalent(*ct) ? result : bad();

        // Otherwise, if there are instance dimemsions left there needs to be packed dimensions
        // in the connection to match up with them.
        if (ct->kind != SymbolKind::PackedArrayType)
            return bad();
    }
    else if (ct->kind != SymbolKind::PackedArrayType) {
        return nullptr;
    }

    // If we reach this point we're looking at a packed array connection; if there were
    // any unpacked dimensions we already stripped them off and accounted for them.
    // The port type must be integral since we're assigning a packed array.
    if (!portType.isIntegral())
        return bad();

    // The width of the port times the number of instances must match the number of bits
    // we have remaining in the connection.
    bitwidth_t numInstances = 1;
    for (auto& dim : instanceDims)
        numInstances *= dim.width();

    bitwidth_t portWidth = portType.getBitWidth();
    auto instPortWidth = checkedMulU32(numInstances, portWidth);
    if (!instPortWidth || *instPortWidth != ct->getBitWidth())
        return bad();

    // Convert the port expression to a simple bit vector so that we can select
    // bit ranges from it -- the range select expression works on the declared
    // range of the packed array so a multidimensional wouldn't work correctly
    // without this conversion.
    result = &ConversionExpression::makeImplicit(
        context, comp.getType(*instPortWidth, result->type->getIntegralFlags()),
        ConversionKind::Implicit, *result, nullptr, {});

    // We have enough bits to assign each port on each instance, so now we just need
    // to pick the right ones. The spec says we start with all right hand indices
    // to match the rightmost part select, iterating through the rightmost dimension first.
    // We know none of these operations will overflow because we already checked that
    // the full size matches the incoming connection above.
    int32_t offset = 0;
    for (size_t i = 0; i < arrayPath.size(); i++) {
        if (i > 0)
            offset *= int32_t(instanceDims[i - 1].width());
        offset += instanceDims[i].translateIndex(arrayPath[i]);
    }

    int32_t width = int32_t(portWidth);
    offset *= width;
    ConstantRange range{offset + width - 1, offset};
    return &RangeSelectExpression::fromConstant(comp, *result, range, context);
}

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
        contextDetermined(context, result, nullptr, t, assignmentRange, /* isAssignment */ true);
    };

    if (type.isEquivalent(*rt)) {
        finalizeType(*rt);

        if (type.isVoid())
            context.addDiag(diag::VoidAssignment, expr.sourceRange);

        // If the types are not actually matching we might still want
        // to issue conversion warnings.
        if (!context.inUnevaluatedBranch() && !type.isMatching(*rt)) {
            checkImplicitConversions(context, *rt, type, *result, nullptr, assignmentRange,
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
        rt = binaryOperatorType(comp, &type, rt, false, /* signednessFromRt */ true);

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

Expression& AssignmentExpression::fromSyntax(Compilation& compilation,
                                             const BinaryExpressionSyntax& syntax,
                                             const ASTContext& context) {
    bitmask<AssignFlags> assignFlags;
    bool isNonBlocking = syntax.kind == SyntaxKind::NonblockingAssignmentExpression;
    if (isNonBlocking)
        assignFlags = AssignFlags::NonBlocking;

    if (isNonBlocking && context.flags.has(ASTFlags::Final)) {
        context.addDiag(diag::NonblockingInFinal, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    if (!context.flags.has(ASTFlags::AssignmentAllowed)) {
        if (!context.flags.has(ASTFlags::NonProcedural) &&
            !context.flags.has(ASTFlags::AssignmentDisallowed)) {
            context.addDiag(diag::AssignmentRequiresParens, syntax.sourceRange());
        }
        else {
            context.addDiag(diag::AssignmentNotAllowed, syntax.sourceRange());
        }
        return badExpr(compilation, nullptr);
    }

    bitmask<ASTFlags> extraFlags = ASTFlags::None;
    std::optional<BinaryOperator> op;
    if (syntax.kind != SyntaxKind::AssignmentExpression &&
        syntax.kind != SyntaxKind::NonblockingAssignmentExpression) {
        op = getBinaryOperator(syntax.kind);
    }
    else {
        extraFlags |= ASTFlags::StreamingAllowed;
    }

    const ExpressionSyntax* rightExpr = syntax.right;

    // If we're in a top-level statement, check for an intra-assignment timing control.
    // Otherwise, we'll let this fall through to the default handler which will issue an error.
    const TimingControl* timingControl = nullptr;
    if (context.flags.has(ASTFlags::TopLevelStatement) &&
        rightExpr->kind == SyntaxKind::TimingControlExpression) {

        ASTContext timingCtx = context;
        timingCtx.flags |= ASTFlags::LValue;
        if (isNonBlocking)
            timingCtx.flags |= ASTFlags::NonBlockingTimingControl;

        auto& tce = rightExpr->as<TimingControlExpressionSyntax>();
        timingControl = &TimingControl::bind(*tce.timing, timingCtx);
        rightExpr = tce.expr;
    }

    // The right hand side of an assignment expression is typically an
    // "assignment-like context", except if the left hand side does not
    // have a self-determined type. That can only be true if the lhs is
    // an assignment pattern without an explicit type.
    // However, streaming concatenation has no explicit type either so it is excluded and such right
    // hand side will lead to diag::AssignmentPatternNoContext error later.
    if (syntax.left->kind == SyntaxKind::AssignmentPatternExpression &&
        rightExpr->kind != SyntaxKind::StreamingConcatenationExpression) {
        auto& pattern = syntax.left->as<AssignmentPatternExpressionSyntax>();
        if (!pattern.type) {
            // In this case we have to bind the rhs first to determine the
            // correct type to use as the context for the lhs.
            auto rhs = &selfDetermined(compilation, *rightExpr, context);
            auto lhs = &create(compilation, *syntax.left, context, ASTFlags::LValue, rhs->type);
            selfDetermined(context, lhs);

            return fromComponents(compilation, op, assignFlags, *lhs, *rhs,
                                  syntax.operatorToken.range(), timingControl, syntax.sourceRange(),
                                  context);
        }
    }

    auto& lhs = selfDetermined(compilation, *syntax.left, context, extraFlags | ASTFlags::LValue);

    Expression* rhs = nullptr;
    if (lhs.type->isVirtualInterfaceOrArray())
        rhs = tryBindInterfaceRef(context, *rightExpr, /* isInterfacePort */ false);

    if (!rhs) {
        // When LHS is a streaming concatenation which has no explicit type, RHS should be
        // self-determined and we cannot pass lsh.type to it. When both LHS and RHS are streaming
        // concatenations, pass lhs.type to notify RHS to exclude associative arrays for
        // isBitstreamType check, while RHS can still be self-determined by ignoring lhs type
        // information.
        if (lhs.kind == ExpressionKind::Streaming &&
            rightExpr->kind != SyntaxKind::StreamingConcatenationExpression) {
            rhs = &selfDetermined(compilation, *rightExpr, context, extraFlags);
        }
        else {
            rhs = &create(compilation, *rightExpr, context, extraFlags, lhs.type);
        }
    }

    return fromComponents(compilation, op, assignFlags, lhs, *rhs, syntax.operatorToken.range(),
                          timingControl, syntax.sourceRange(), context);
}

Expression& AssignmentExpression::fromComponents(
    Compilation& compilation, std::optional<BinaryOperator> op, bitmask<AssignFlags> flags,
    Expression& lhs, Expression& rhs, SourceRange opRange, const TimingControl* timingControl,
    SourceRange sourceRange, const ASTContext& context) {

    auto result = compilation.emplace<AssignmentExpression>(op, flags.has(AssignFlags::NonBlocking),
                                                            *lhs.type, lhs, rhs, timingControl,
                                                            sourceRange);

    if (lhs.bad() || rhs.bad())
        return badExpr(compilation, result);

    if (lhs.kind == ExpressionKind::Streaming) {
        if (!Bitstream::canBeTarget(lhs.as<StreamingConcatenationExpression>(), rhs, opRange,
                                    context)) {
            return badExpr(compilation, result);
        }

        if (!lhs.requireLValue(context, opRange.start(), flags))
            return badExpr(compilation, result);

        return *result;
    }

    // If this is a compound assignment operator create a binary expression that will
    // apply the operator for us on the right hand side.
    if (op) {
        auto lvalRef = compilation.emplace<LValueReferenceExpression>(*lhs.type, lhs.sourceRange);
        result->right_ = &BinaryExpression::fromComponents(*lvalRef, *result->right_, *op, opRange,
                                                           sourceRange, context);
    }

    result->right_ = &convertAssignment(context, *lhs.type, *result->right_, opRange,
                                        &result->left_, &flags);
    if (result->right_->bad())
        return badExpr(compilation, result);

    if (!result->left_->requireLValue(context, opRange.start(), flags))
        return badExpr(compilation, result);

    if (timingControl) {
        // Cycle delays are only allowed on clock vars, and clock vars
        // cannot use any timing control other than cycle delays.
        if (auto sym = lhs.getSymbolReference(); sym && sym->kind == SymbolKind::ClockVar) {
            if (timingControl->kind != TimingControlKind::CycleDelay) {
                SLANG_ASSERT(timingControl->syntax);
                context.addDiag(diag::ClockVarBadTiming, timingControl->syntax->sourceRange());
            }
        }
        else if (timingControl->kind == TimingControlKind::CycleDelay) {
            SLANG_ASSERT(timingControl->syntax);
            context.addDiag(diag::CycleDelayNonClock, timingControl->syntax->sourceRange());
        }
    }

    return *result;
}

bool AssignmentExpression::isLValueArg() const {
    return right().kind == ExpressionKind::EmptyArgument ||
           (right().kind == ExpressionKind::Conversion &&
            right().as<ConversionExpression>().operand().kind == ExpressionKind::EmptyArgument);
}

ConstantValue AssignmentExpression::evalImpl(EvalContext& context) const {
    if (!context.flags.has(EvalFlags::IsScript) && timingControl) {
        context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
        return nullptr;
    }

    if (left().kind == ExpressionKind::Streaming) {
        return Bitstream::evaluateTarget(left().as<StreamingConcatenationExpression>(), right(),
                                         context);
    }

    LValue lvalue = left().evalLValue(context);
    if (!lvalue)
        return nullptr;

    if (isCompound())
        context.pushLValue(lvalue);

    ConstantValue rvalue = right().eval(context);

    if (isCompound())
        context.popLValue();

    if (!rvalue)
        return nullptr;

    lvalue.store(rvalue);
    return rvalue;
}

void AssignmentExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("left", left());
    serializer.write("right", right());
    serializer.write("isNonBlocking", isNonBlocking());
    if (op)
        serializer.write("op", toString(*op));
    if (timingControl)
        serializer.write("timingControl", *timingControl);
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
        selfDetermined(context, operand);

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

        operand = &selfDetermined(comp, *syntax.right, context, ASTFlags::StreamingAllowed);
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
    if (type->isMatching(*operand->type) &&
        ((assignmentTarget && assignmentTarget->isMatching(*type)) ||
         !actuallyNeededCast(*type, *operand))) {
        context.addDiag(diag::UselessCast, syntax.apostrophe.location())
            << *operand->type << targetExpr.sourceRange << operand->sourceRange;
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
    return convert(context, *operand().type, *type, sourceRange, operand().eval(context),
                   conversionKind, &operand(), implicitOpRange);
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

Expression& NewArrayExpression::fromSyntax(Compilation& compilation,
                                           const NewArrayExpressionSyntax& syntax,
                                           const ASTContext& context,
                                           const Type* assignmentTarget) {
    if (!assignmentTarget ||
        assignmentTarget->getCanonicalType().kind != SymbolKind::DynamicArrayType) {

        if (!assignmentTarget || !assignmentTarget->isError())
            context.addDiag(diag::NewArrayTarget, syntax.sourceRange());

        if (!assignmentTarget)
            assignmentTarget = &compilation.getErrorType();
    }

    auto& sizeExpr = selfDetermined(compilation, *syntax.sizeExpr, context);
    const Expression* initExpr = nullptr;
    if (syntax.initializer)
        initExpr = &bindRValue(*assignmentTarget, *syntax.initializer->expression, {}, context);

    auto result = compilation.emplace<NewArrayExpression>(*assignmentTarget, sizeExpr, initExpr,
                                                          syntax.sourceRange());
    if (sizeExpr.bad() || (initExpr && initExpr->bad()))
        return badExpr(compilation, result);

    if (!context.requireIntegral(sizeExpr))
        return badExpr(compilation, result);

    return *result;
}

ConstantValue NewArrayExpression::evalImpl(EvalContext& context) const {
    ConstantValue sz = sizeExpr().eval(context);
    if (!sz)
        return nullptr;

    std::optional<int64_t> size = sz.integer().as<int64_t>();
    if (!size || *size < 0) {
        context.addDiag(diag::InvalidArraySize, sizeExpr().sourceRange) << sz;
        return nullptr;
    }

    size_t count = size_t(*size);
    size_t index = 0;
    std::vector<ConstantValue> result(count);

    ConstantValue iv;
    if (initExpr()) {
        iv = initExpr()->eval(context);
        if (!iv)
            return nullptr;

        auto elems = iv.elements();
        for (; index < count && index < elems.size(); index++)
            result[index] = elems[index];
    }

    // Any remaining elements are default initialized.
    ConstantValue def = type->getArrayElementType()->getDefaultValue();
    for (; index < count; index++)
        result[index] = def;

    return result;
}

void NewArrayExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("sizeExpr", sizeExpr());
    if (initExpr())
        serializer.write("initExpr", *initExpr());
}

static std::pair<const ClassType*, bool> resolveNewClassTarget(const NameSyntax& nameSyntax,
                                                               const ASTContext& context,
                                                               const Type*& assignmentTarget,
                                                               SourceRange range) {
    // If the new expression is typed, look up that type as the target.
    // Otherwise, the target must come from the expression context.
    bool isSuperClass = false;
    const ClassType* classType = nullptr;
    if (nameSyntax.kind == SyntaxKind::ConstructorName) {
        if (!assignmentTarget || !assignmentTarget->isClass()) {
            if (!assignmentTarget || !assignmentTarget->isError())
                context.addDiag(diag::NewClassTarget, range);
            return {nullptr, false};
        }

        classType = &assignmentTarget->getCanonicalType().as<ClassType>();
    }
    else {
        auto& scoped = nameSyntax.as<ScopedNameSyntax>();
        if (scoped.left->getLastToken().kind == TokenKind::SuperKeyword) {
            // This is a super.new invocation, so find the base class's
            // constructor. This is relative to our current context, not
            // any particular assignment target.
            auto [ct, _] = Lookup::getContainingClass(*context.scope);
            classType = ct;
            if (!classType || classType->name.empty()) {
                // Parser already emitted an error for this case.
                return {nullptr, false};
            }

            auto base = classType->getBaseClass();
            if (!base) {
                context.addDiag(diag::SuperNoBase, nameSyntax.sourceRange()) << classType->name;
                return {nullptr, false};
            }

            if (base->isError())
                return {nullptr, false};

            classType = &base->as<Type>().getCanonicalType().as<ClassType>();
            assignmentTarget = &context.getCompilation().getVoidType();
            isSuperClass = true;
        }
        else {
            auto& className = *nameSyntax.as<ScopedNameSyntax>().left;
            classType = Lookup::findClass(className, context);
            if (!classType)
                return {nullptr, false};

            assignmentTarget = classType;
        }
    }

    if (!isSuperClass && classType->isAbstract) {
        context.addDiag(diag::NewVirtualClass, range) << classType->name;
        return {nullptr, false};
    }

    if (!isSuperClass && classType->isInterface) {
        context.addDiag(diag::NewInterfaceClass, range) << classType->name;
        return {nullptr, false};
    }

    return {classType, isSuperClass};
}

Expression& NewClassExpression::fromSyntax(Compilation& comp,
                                           const NewClassExpressionSyntax& syntax,
                                           const ASTContext& context,
                                           const Type* assignmentTarget) {
    // The new keyword can also be used to create covergroups.
    if (syntax.scopedNew->kind == SyntaxKind::ConstructorName && assignmentTarget &&
        assignmentTarget->isCovergroup()) {
        return NewCovergroupExpression::fromSyntax(comp, syntax, context, *assignmentTarget);
    }

    SourceRange range = syntax.sourceRange();
    auto [classType, isSuperClass] = resolveNewClassTarget(*syntax.scopedNew, context,
                                                           assignmentTarget, range);
    if (!classType)
        return badExpr(comp, nullptr);

    Expression* constructorCall = nullptr;
    if (auto constructor = classType->getConstructor()) {
        Lookup::ensureVisible(*constructor, context, range);
        constructorCall = &CallExpression::fromArgs(comp, &constructor->as<SubroutineSymbol>(),
                                                    nullptr, syntax.argList, range, context);
    }
    else if (syntax.argList && !syntax.argList->parameters.empty()) {
        auto& diag = context.addDiag(diag::TooManyArguments, syntax.argList->sourceRange());
        diag << "new"sv;
        diag << 0;
        diag << syntax.argList->parameters.size();
    }

    return *comp.emplace<NewClassExpression>(*assignmentTarget, constructorCall, isSuperClass,
                                             range);
}

Expression& NewClassExpression::fromSyntax(Compilation& comp,
                                           const SuperNewDefaultedArgsExpressionSyntax& syntax,
                                           const ASTContext& context,
                                           const Type* assignmentTarget) {
    SourceRange range = syntax.sourceRange();
    auto [classType, isSuperClass] = resolveNewClassTarget(*syntax.scopedNew, context,
                                                           assignmentTarget, range);
    if (!classType)
        return badExpr(comp, nullptr);

    SLANG_ASSERT(isSuperClass);

    // The containing constructor (should be our parent scope)
    // must have a 'default' argument as well.
    if (context.scope->asSymbol().kind == SymbolKind::Subroutine) {
        auto& sub = context.scope->asSymbol().as<SubroutineSymbol>();
        if (!sub.flags.has(MethodFlags::DefaultedSuperArg))
            context.addDiag(diag::InvalidSuperNewDefault, range);
    }

    return *comp.emplace<NewClassExpression>(*assignmentTarget, nullptr, isSuperClass, range);
}

ConstantValue NewClassExpression::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalClassType, sourceRange);
    return nullptr;
}

void NewClassExpression::serializeTo(ASTSerializer& serializer) const {
    if (constructorCall())
        serializer.write("constructorCall", *constructorCall());
    serializer.write("isSuperClass", isSuperClass);
}

Expression& NewCovergroupExpression::fromSyntax(Compilation& compilation,
                                                const NewClassExpressionSyntax& syntax,
                                                const ASTContext& context,
                                                const Type& assignmentTarget) {
    auto range = syntax.sourceRange();
    auto& coverType = assignmentTarget.getCanonicalType().as<CovergroupType>();

    SmallVector<const Expression*> args;
    if (!CallExpression::bindArgs(syntax.argList, coverType.getArguments(), "new"sv, range, context,
                                  args, /* isBuiltInMethod */ false)) {
        return badExpr(compilation, nullptr);
    }

    return *compilation.emplace<NewCovergroupExpression>(assignmentTarget, args.copy(compilation),
                                                         range);
}

ConstantValue NewCovergroupExpression::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalCovergroupType, sourceRange);
    return nullptr;
}

void NewCovergroupExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("arguments");
    for (auto arg : arguments)
        serializer.serialize(*arg);
    serializer.endArray();
}

Expression& Expression::bindAssignmentPattern(Compilation& comp,
                                              const AssignmentPatternExpressionSyntax& syntax,
                                              const ASTContext& context,
                                              const Type* assignmentTarget) {
    SourceRange range = syntax.sourceRange();

    if (syntax.type) {
        assignmentTarget = &comp.getType(*syntax.type, context);
        if (!assignmentTarget->isSimpleType() && syntax.type->kind != SyntaxKind::TypeReference) {
            if (!assignmentTarget->isError())
                context.addDiag(diag::BadAssignmentPatternType, range) << *assignmentTarget;
            return badExpr(comp, nullptr);
        }
    }

    if (!assignmentTarget || assignmentTarget->isError()) {
        if (!assignmentTarget)
            context.addDiag(diag::AssignmentPatternNoContext, syntax.sourceRange());
        return badExpr(comp, nullptr);
    }

    const Type& type = *assignmentTarget;
    const Scope* structScope = nullptr;
    const Type* elementType = nullptr;
    bitwidth_t numElements = 0;

    auto& ct = type.getCanonicalType();
    if (ct.kind == SymbolKind::PackedStructType) {
        structScope = &ct.as<PackedStructType>();
    }
    else if (ct.kind == SymbolKind::UnpackedStructType) {
        structScope = &ct.as<UnpackedStructType>();
    }
    else if (ct.kind == SymbolKind::PackedArrayType) {
        auto& ua = ct.as<PackedArrayType>();
        elementType = &ua.elementType;
        numElements = ua.range.width();
    }
    else if (ct.kind == SymbolKind::FixedSizeUnpackedArrayType) {
        auto& ua = ct.as<FixedSizeUnpackedArrayType>();
        elementType = &ua.elementType;
        numElements = ua.range.width();
    }
    else if (ct.kind == SymbolKind::DynamicArrayType ||
             ct.kind == SymbolKind::AssociativeArrayType || ct.kind == SymbolKind::QueueType) {
        elementType = ct.getArrayElementType();
    }
    else if (ct.isIntegral() && ct.kind != SymbolKind::ScalarType) {
        elementType = ct.isFourState() ? &comp.getLogicType() : &comp.getBitType();
        numElements = ct.getBitWidth();
    }
    else {
        context.addDiag(diag::BadAssignmentPatternType, range) << type;
        return badExpr(comp, nullptr);
    }

    const AssignmentPatternSyntax& p = *syntax.pattern;
    if (context.flags.has(ASTFlags::LValue) && p.kind != SyntaxKind::SimpleAssignmentPattern) {
        context.addDiag(diag::ExpressionNotAssignable, range);
        return badExpr(comp, nullptr);
    }

    if (structScope) {
        switch (p.kind) {
            case SyntaxKind::SimpleAssignmentPattern:
                return SimpleAssignmentPatternExpression::forStruct(
                    comp, p.as<SimpleAssignmentPatternSyntax>(), context, type, *structScope,
                    range);
            case SyntaxKind::StructuredAssignmentPattern:
                return StructuredAssignmentPatternExpression::forStruct(
                    comp, p.as<StructuredAssignmentPatternSyntax>(), context, type, *structScope,
                    range);
            case SyntaxKind::ReplicatedAssignmentPattern:
                return ReplicatedAssignmentPatternExpression::forStruct(
                    comp, p.as<ReplicatedAssignmentPatternSyntax>(), context, type, *structScope,
                    range);
            default:
                SLANG_UNREACHABLE;
        }
    }
    else if (ct.kind == SymbolKind::DynamicArrayType || ct.kind == SymbolKind::QueueType) {
        switch (p.kind) {
            case SyntaxKind::SimpleAssignmentPattern:
                return SimpleAssignmentPatternExpression::forDynamicArray(
                    comp, p.as<SimpleAssignmentPatternSyntax>(), context, type, *elementType,
                    range);
            case SyntaxKind::StructuredAssignmentPattern:
                return StructuredAssignmentPatternExpression::forDynamicArray(
                    comp, p.as<StructuredAssignmentPatternSyntax>(), context, type, *elementType,
                    range);
            case SyntaxKind::ReplicatedAssignmentPattern:
                return ReplicatedAssignmentPatternExpression::forDynamicArray(
                    comp, p.as<ReplicatedAssignmentPatternSyntax>(), context, type, *elementType,
                    range);
            default:
                SLANG_UNREACHABLE;
        }
    }
    else if (ct.kind == SymbolKind::AssociativeArrayType) {
        switch (p.kind) {
            case SyntaxKind::SimpleAssignmentPattern:
            case SyntaxKind::ReplicatedAssignmentPattern:
                context.addDiag(diag::AssignmentPatternAssociativeType, range);
                return badExpr(comp, nullptr);
            case SyntaxKind::StructuredAssignmentPattern:
                return StructuredAssignmentPatternExpression::forAssociativeArray(
                    comp, p.as<StructuredAssignmentPatternSyntax>(), context, type, *elementType,
                    range);
            default:
                SLANG_UNREACHABLE;
        }
    }
    else {
        switch (p.kind) {
            case SyntaxKind::SimpleAssignmentPattern:
                return SimpleAssignmentPatternExpression::forFixedArray(
                    comp, p.as<SimpleAssignmentPatternSyntax>(), context, type, *elementType,
                    numElements, range);
            case SyntaxKind::StructuredAssignmentPattern:
                return StructuredAssignmentPatternExpression::forFixedArray(
                    comp, p.as<StructuredAssignmentPatternSyntax>(), context, type, *elementType,
                    range);
            case SyntaxKind::ReplicatedAssignmentPattern:
                return ReplicatedAssignmentPatternExpression::forFixedArray(
                    comp, p.as<ReplicatedAssignmentPatternSyntax>(), context, type, *elementType,
                    numElements, range);
            default:
                SLANG_UNREACHABLE;
        }
    }
}

ConstantValue AssignmentPatternExpressionBase::evalImpl(EvalContext& context) const {
    size_t replCount = 1;
    if (kind == ExpressionKind::ReplicatedAssignmentPattern) {
        auto countVal = as<ReplicatedAssignmentPatternExpression>()
                            .count()
                            .eval(context)
                            .integer()
                            .as<int32_t>();
        SLANG_ASSERT(countVal >= 0);
        replCount = size_t(*countVal);
    }

    if (type->isIntegral()) {
        SmallVector<SVInt> values;
        for (size_t i = 0; i < replCount; i++) {
            for (auto elem : elements()) {
                ConstantValue v = elem->eval(context);
                if (!v)
                    return nullptr;

                values.push_back(v.integer());
            }
        }

        return SVInt::concat(values);
    }
    else if (type->isAssociativeArray()) {
        // Special casing for associative arrays: there is no contiguous set of
        // elements, so downcast to the known type (must be a Structured pattern)
        // and build the map from the index setters.
        AssociativeArray values;
        auto& sap = as<StructuredAssignmentPatternExpression>();
        for (auto& setter : sap.indexSetters) {
            SLANG_ASSERT(setter.expr && setter.index);
            ConstantValue key = setter.index->eval(context);
            ConstantValue val = setter.expr->eval(context);
            if (!key || !val)
                return nullptr;

            values.try_emplace(std::move(key), std::move(val));
        }

        if (sap.defaultSetter) {
            values.defaultValue = sap.defaultSetter->eval(context);
            if (!values.defaultValue)
                return nullptr;
        }

        return values;
    }
    else if (type->isQueue()) {
        SVQueue result;
        result.maxBound = type->getCanonicalType().as<QueueType>().maxBound;
        for (size_t i = 0; i < replCount; i++) {
            for (auto elem : elements()) {
                result.emplace_back(elem->eval(context));
                if (result.back().bad())
                    return nullptr;
            }
        }

        result.resizeToBound();
        return result;
    }
    else {
        std::vector<ConstantValue> values;
        for (size_t i = 0; i < replCount; i++) {
            for (auto elem : elements()) {
                values.emplace_back(elem->eval(context));
                if (values.back().bad())
                    return nullptr;
            }
        }

        return values;
    }
}

void AssignmentPatternExpressionBase::serializeTo(ASTSerializer& serializer) const {
    if (!elements().empty()) {
        serializer.startArray("elements");
        for (auto elem : elements())
            serializer.serialize(*elem);
        serializer.endArray();
    }
}

Expression& SimpleAssignmentPatternExpression::forStruct(
    Compilation& comp, const SimpleAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Scope& structScope, SourceRange sourceRange) {

    SmallVector<const Type*> types;
    for (auto& field : structScope.membersOfType<FieldSymbol>())
        types.push_back(&field.getType());

    if (types.size() != syntax.items.size()) {
        auto& diag = context.addDiag(diag::WrongNumberAssignmentPatterns, sourceRange);
        diag << type << types.size() << syntax.items.size();
        return badExpr(comp, nullptr);
    }

    const bool isLValue = context.flags.has(ASTFlags::LValue);
    auto direction = isLValue ? ArgumentDirection::Out : ArgumentDirection::In;

    bool bad = false;
    uint32_t index = 0;
    SmallVector<const Expression*> elems;
    for (auto item : syntax.items) {
        auto& expr = Expression::bindArgument(*types[index++], direction, {}, *item, context);
        elems.push_back(&expr);
        bad |= expr.bad();
    }

    auto result = comp.emplace<SimpleAssignmentPatternExpression>(type, isLValue, elems.copy(comp),
                                                                  sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

static std::span<const Expression* const> bindExpressionList(
    const Type& patternType, const Type& elementType, size_t replCount, bitwidth_t expectedCount,
    const SeparatedSyntaxList<ExpressionSyntax>& items, const ASTContext& context,
    SourceRange sourceRange, bool& bad) {

    const bool isLValue = context.flags.has(ASTFlags::LValue);
    auto direction = isLValue ? ArgumentDirection::Out : ArgumentDirection::In;

    SmallVector<const Expression*> elems;
    for (auto item : items) {
        auto& expr = Expression::bindArgument(elementType, direction, {}, *item, context);
        elems.push_back(&expr);
        bad |= expr.bad();
    }

    if (!bad && expectedCount && expectedCount != elems.size() * replCount) {
        auto& diag = context.addDiag(diag::WrongNumberAssignmentPatterns, sourceRange);
        diag << patternType << expectedCount << elems.size();
        bad = true;
    }

    return elems.copy(context.getCompilation());
}

Expression& SimpleAssignmentPatternExpression::forFixedArray(
    Compilation& comp, const SimpleAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, bitwidth_t numElements, SourceRange sourceRange) {

    bool bad = false;
    auto elems = bindExpressionList(type, elementType, 1, numElements, syntax.items, context,
                                    sourceRange, bad);

    const bool isLValue = context.flags.has(ASTFlags::LValue);
    auto result = comp.emplace<SimpleAssignmentPatternExpression>(type, isLValue, elems,
                                                                  sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& SimpleAssignmentPatternExpression::forDynamicArray(
    Compilation& comp, const SimpleAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    const bool isLValue = context.flags.has(ASTFlags::LValue);
    if (isLValue) {
        context.addDiag(diag::AssignmentPatternLValueDynamic, sourceRange);
        return badExpr(comp, nullptr);
    }

    bool bad = false;
    auto elems = bindExpressionList(type, elementType, 1, 0, syntax.items, context, sourceRange,
                                    bad);

    auto result = comp.emplace<SimpleAssignmentPatternExpression>(type, isLValue, elems,
                                                                  sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

LValue SimpleAssignmentPatternExpression::evalLValueImpl(EvalContext& context) const {
    std::vector<LValue> lvals;
    lvals.reserve(elements().size());
    for (auto elem : elements()) {
        LValue lval = elem->as<AssignmentExpression>().left().evalLValue(context);
        if (!lval)
            return nullptr;

        lvals.emplace_back(std::move(lval));
    }

    auto lvalKind = type->isIntegral() ? LValue::Concat::Packed : LValue::Concat::Unpacked;
    return LValue(std::move(lvals), lvalKind);
}

static const Expression* matchElementValue(
    const ASTContext& context, const Type& elementType, const FieldSymbol* targetField,
    SourceRange sourceRange,
    std::span<const StructuredAssignmentPatternExpression::TypeSetter> typeSetters,
    const Expression* defaultSetter) {

    // Every element in the array or structure must be covered by one of:
    // index:value      -- recorded in the indexMap (handled only at the top level, not here)
    // member:value     -- recorded in the memberMap (handled only at the top level, not here)
    // type:value       -- recorded in typeSetters, last one takes precedence
    // default:value    -- recorded in defaultSetter, types must be assignable
    // struct element   -- recursively descend into the struct
    // array element    -- recursively descend into the array

    if (elementType.isError())
        return nullptr;

    // Try all type setters for a match. Last one that matches wins.
    const Expression* found = nullptr;
    for (auto& setter : typeSetters) {
        if (setter.type && elementType.isMatching(*setter.type))
            found = setter.expr;
    }
    if (found)
        return found;

    // Otherwise, see if we have a default value that can be applied.
    // The default applies if:
    // - The element type matches exactly
    // - The element type is a simple bit vector and the type is assignment compatible
    const ExpressionSyntax* defaultSyntax = nullptr;
    if (defaultSetter) {
        defaultSyntax = defaultSetter->syntax;
        SLANG_ASSERT(defaultSyntax);
    }

    if (defaultSetter) {
        if (elementType.isMatching(*defaultSetter->type))
            return defaultSetter;

        if (elementType.isSimpleBitVector() &&
            elementType.isAssignmentCompatible(*defaultSetter->type)) {
            return &Expression::bindRValue(elementType, *defaultSyntax, {}, context);
        }
    }

    // Otherwise, we check first if the type is a struct or array, in which
    // case we descend recursively into its members before continuing on with the default.
    if (elementType.isStruct()) {
        const Scope* structScope;
        if (elementType.isUnpackedStruct())
            structScope = &elementType.getCanonicalType().as<UnpackedStructType>();
        else
            structScope = &elementType.getCanonicalType().as<PackedStructType>();

        SmallVector<const Expression*> elements;
        for (auto& field : structScope->membersOfType<FieldSymbol>()) {
            const Type& type = field.getType();
            if (type.isError() || field.name.empty())
                return nullptr;

            auto elemExpr = matchElementValue(context, type, &field, sourceRange, typeSetters,
                                              defaultSetter);
            if (!elemExpr)
                return nullptr;

            elements.push_back(elemExpr);
        }

        auto& comp = context.getCompilation();
        return comp.emplace<SimpleAssignmentPatternExpression>(elementType, /* isLValue */ false,
                                                               elements.copy(comp), sourceRange);
    }

    if (elementType.isArray() && elementType.hasFixedRange()) {
        auto nestedElemType = elementType.getArrayElementType();
        SLANG_ASSERT(nestedElemType);

        auto elemExpr = matchElementValue(context, *nestedElemType, nullptr, sourceRange,
                                          typeSetters, defaultSetter);
        if (!elemExpr)
            return nullptr;

        SmallVector<const Expression*> elements;
        auto arrayRange = elementType.getFixedRange();
        for (int32_t i = arrayRange.lower(); i <= arrayRange.upper(); i++)
            elements.push_back(elemExpr);

        auto& comp = context.getCompilation();
        return comp.emplace<SimpleAssignmentPatternExpression>(elementType, /* isLValue */ false,
                                                               elements.copy(comp), sourceRange);
    }

    // Finally, if we have a default then it must now be assignment compatible.
    if (defaultSetter)
        return &Expression::bindRValue(elementType, *defaultSyntax, {}, context);

    // Otherwise there's no setter for this element, which is an error.
    if (targetField) {
        auto& diag = context.addDiag(diag::AssignmentPatternNoMember, sourceRange);
        diag << targetField->name;
        diag.addNote(diag::NoteDeclarationHere, targetField->location);
    }
    else {
        context.addDiag(diag::AssignmentPatternMissingElements, sourceRange);
    }

    return nullptr;
}

Expression& StructuredAssignmentPatternExpression::forStruct(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Scope& structScope, SourceRange sourceRange) {

    bool bad = false;
    const Expression* defaultSetter = nullptr;
    SmallMap<const Symbol*, const Expression*, 8> memberMap;
    SmallVector<MemberSetter, 4> memberSetters;
    SmallVector<TypeSetter, 4> typeSetters;

    for (auto item : syntax.items) {
        if (item->key->kind == SyntaxKind::DefaultPatternKeyExpression) {
            if (defaultSetter) {
                context.addDiag(diag::AssignmentPatternKeyDupDefault, item->key->sourceRange());
                bad = true;
            }
            defaultSetter = &selfDetermined(comp, *item->expr, context);
            bad |= defaultSetter->bad();
        }
        else if (item->key->kind == SyntaxKind::IdentifierName) {
            auto nameToken = item->key->as<IdentifierNameSyntax>().identifier;
            auto name = nameToken.valueText();
            if (name.empty()) {
                bad = true;
                continue;
            }

            const Symbol* member = structScope.find(name);
            if (member) {
                auto& expr = bindRValue(member->as<FieldSymbol>().getType(), *item->expr,
                                        nameToken.range(), context);
                bad |= expr.bad();

                auto [it, inserted] = memberMap.emplace(member, &expr);
                if (!inserted) {
                    auto& diag = context.addDiag(diag::AssignmentPatternKeyDupName,
                                                 item->key->sourceRange());
                    diag << name;
                    diag.addNote(diag::NotePreviousDefinition, it->second->sourceRange);
                    bad = true;
                    continue;
                }

                memberSetters.emplace_back(MemberSetter{member, &expr});
            }
            else {
                auto found = Lookup::unqualified(*context.scope, name, LookupFlags::Type);
                if (found && found->isType()) {
                    auto& expr = bindRValue(found->as<Type>(), *item->expr, nameToken.range(),
                                            context);
                    bad |= expr.bad();

                    typeSetters.emplace_back(TypeSetter{&found->as<Type>(), &expr});
                }
                else {
                    auto& diag = context.addDiag(diag::UnknownMember, item->key->sourceRange());
                    diag << name;
                    diag << type;
                    bad = true;
                }
            }
        }
        else if (DataTypeSyntax::isKind(item->key->kind)) {
            const Type& typeKey = comp.getType(item->key->as<DataTypeSyntax>(), context);
            if (typeKey.isSimpleType()) {
                auto& expr = bindRValue(typeKey, *item->expr, {}, context);
                typeSetters.emplace_back(TypeSetter{&typeKey, &expr});
                bad |= expr.bad();
            }
            else {
                context.addDiag(diag::AssignmentPatternKeyExpr, item->key->sourceRange());
                bad = true;
            }
        }
        else {
            context.addDiag(diag::AssignmentPatternKeyExpr, item->key->sourceRange());
            bad = true;
        }
    }

    SmallVector<const Expression*> elements;
    for (auto& field : structScope.membersOfType<FieldSymbol>()) {
        // If we already have a setter for this field we don't have to do anything else.
        if (auto it = memberMap.find(&field); it != memberMap.end()) {
            elements.push_back(it->second);
            continue;
        }

        const Type& fieldType = field.getType();
        if (fieldType.isError() || field.name.empty()) {
            bad = true;
            continue;
        }

        auto expr = matchElementValue(context, fieldType, &field, sourceRange, typeSetters,
                                      defaultSetter);
        if (!expr) {
            bad = true;
            continue;
        }

        elements.push_back(expr);
    }

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, memberSetters.copy(comp), typeSetters.copy(comp), std::span<const IndexSetter>{},
        defaultSetter, elements.copy(comp), sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

static std::optional<int32_t> bindArrayIndexSetter(
    const ASTContext& context, const Expression& keyExpr, const Type& elementType,
    const ExpressionSyntax& valueSyntax, SmallMap<int32_t, const Expression*, 8>& indexMap,
    SmallVectorBase<StructuredAssignmentPatternExpression::IndexSetter>& indexSetters) {

    std::optional<int32_t> index = context.evalInteger(keyExpr);
    if (!index)
        return std::nullopt;

    auto& expr = Expression::bindRValue(elementType, valueSyntax, {}, context);
    if (expr.bad())
        return std::nullopt;

    auto [it, inserted] = indexMap.emplace(*index, &expr);
    if (!inserted) {
        auto& diag = context.addDiag(diag::AssignmentPatternKeyDupValue, keyExpr.sourceRange);
        diag << *index;
        diag.addNote(diag::NotePreviousDefinition, it->second->sourceRange);
        return std::nullopt;
    }

    indexSetters.push_back({&keyExpr, &expr});
    return index;
}

Expression& StructuredAssignmentPatternExpression::forFixedArray(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    bool bad = false;
    const Expression* defaultSetter = nullptr;
    SmallMap<int32_t, const Expression*, 8> indexMap;
    SmallVector<IndexSetter, 4> indexSetters;
    SmallVector<TypeSetter, 4> typeSetters;

    for (auto item : syntax.items) {
        if (item->key->kind == SyntaxKind::DefaultPatternKeyExpression) {
            if (defaultSetter) {
                context.addDiag(diag::AssignmentPatternKeyDupDefault, item->key->sourceRange());
                bad = true;
            }
            defaultSetter = &selfDetermined(comp, *item->expr, context);
            bad |= defaultSetter->bad();
            continue;
        }

        // The key is either an array index or a data type setter.
        auto& keyExpr = Expression::bind(*item->key, context, ASTFlags::AllowDataType);
        if (keyExpr.bad()) {
            bad = true;
            continue;
        }

        if (keyExpr.kind == ExpressionKind::DataType) {
            const Type& typeKey = *keyExpr.type;
            if (typeKey.isSimpleType()) {
                auto& expr = bindRValue(typeKey, *item->expr, {}, context);
                typeSetters.emplace_back(TypeSetter{&typeKey, &expr});
                bad |= expr.bad();
            }
            else {
                context.addDiag(diag::AssignmentPatternKeyExpr, item->key->sourceRange());
                bad = true;
            }
        }
        else {
            auto index = bindArrayIndexSetter(context, keyExpr, elementType, *item->expr, indexMap,
                                              indexSetters);
            if (!index) {
                bad = true;
                continue;
            }

            if (!type.getFixedRange().containsPoint(*index)) {
                auto& diag = context.addDiag(diag::IndexValueInvalid, keyExpr.sourceRange);
                diag << *index;
                diag << type;
                bad = true;
            }
        }
    }

    SmallVector<const Expression*> elements;
    std::optional<const Expression*> cachedVal;
    auto arrayRange = type.getFixedRange();

    for (int32_t i = arrayRange.lower(); i <= arrayRange.upper(); i++) {
        // If we already have a setter for this index we don't have to do anything else.
        if (auto it = indexMap.find(i); it != indexMap.end()) {
            elements.push_back(it->second);
            continue;
        }

        if (!cachedVal) {
            cachedVal = matchElementValue(context, elementType, nullptr, syntax.sourceRange(),
                                          typeSetters, defaultSetter);
            if (!cachedVal.value()) {
                bad = true;
                break;
            }
        }

        elements.push_back(*cachedVal);
    }

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, std::span<const MemberSetter>{}, typeSetters.copy(comp), indexSetters.copy(comp),
        defaultSetter, elements.copy(comp), sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& StructuredAssignmentPatternExpression::forDynamicArray(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    bool bad = false;
    SmallMap<int32_t, const Expression*, 8> indexMap;
    SmallVector<IndexSetter, 4> indexSetters;
    size_t maxIndex = 0;

    for (auto item : syntax.items) {
        if (item->key->kind == SyntaxKind::DefaultPatternKeyExpression) {
            context.addDiag(diag::AssignmentPatternDynamicDefault, item->key->sourceRange());
            bad = true;
            continue;
        }

        // The key is either an array index or a data type setter.
        auto& keyExpr = Expression::bind(*item->key, context, ASTFlags::AllowDataType);
        if (keyExpr.bad()) {
            bad = true;
            continue;
        }

        if (keyExpr.kind == ExpressionKind::DataType) {
            context.addDiag(diag::AssignmentPatternDynamicType, item->key->sourceRange());
            bad = true;
            continue;
        }

        auto index = bindArrayIndexSetter(context, keyExpr, elementType, *item->expr, indexMap,
                                          indexSetters);
        if (!context.requirePositive(index, keyExpr.sourceRange)) {
            bad = true;
            continue;
        }

        maxIndex = std::max(maxIndex, size_t(*index));
    }

    SmallVector<const Expression*> elements;
    if (indexMap.size() != maxIndex + 1) {
        if (!bad) {
            context.addDiag(diag::AssignmentPatternMissingElements, sourceRange);
            bad = true;
        }
    }
    else {
        elements.reserve(maxIndex + 1);
        for (size_t i = 0; i <= maxIndex; i++) {
            auto expr = indexMap[int32_t(i)];
            SLANG_ASSERT(expr);
            elements.push_back(expr);
        }
    }

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, std::span<const MemberSetter>{}, std::span<const TypeSetter>{},
        indexSetters.copy(comp), nullptr, elements.copy(comp), sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& StructuredAssignmentPatternExpression::forAssociativeArray(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    bool bad = false;
    const Expression* defaultSetter = nullptr;
    SmallVector<IndexSetter, 4> indexSetters;
    SmallMap<ConstantValue, SourceRange, 8> indexMap;

    const Type* indexType = type.getAssociativeIndexType();

    for (auto item : syntax.items) {
        if (item->key->kind == SyntaxKind::DefaultPatternKeyExpression) {
            if (defaultSetter) {
                context.addDiag(diag::AssignmentPatternKeyDupDefault, item->key->sourceRange());
                bad = true;
            }
            defaultSetter = &selfDetermined(comp, *item->expr, context);
            bad |= defaultSetter->bad();
        }
        else if (DataTypeSyntax::isKind(item->key->kind)) {
            context.addDiag(diag::AssignmentPatternDynamicType, item->key->sourceRange());
            bad = true;
        }
        else {
            const Expression* indexExpr;
            if (indexType)
                indexExpr = &bindRValue(*indexType, *item->key, {}, context);
            else
                indexExpr = &Expression::bind(*item->key, context);

            if (!indexExpr->bad()) {
                auto cv = context.eval(*indexExpr);
                if (!cv)
                    bad = true;
                else {
                    auto [it, inserted] = indexMap.emplace(cv, indexExpr->sourceRange);
                    if (!inserted) {
                        auto& diag = context.addDiag(diag::AssignmentPatternKeyDupValue,
                                                     indexExpr->sourceRange);
                        diag << cv;
                        diag.addNote(diag::NotePreviousDefinition, it->second);
                        bad = true;
                    }
                }
            }

            auto& expr = bindRValue(elementType, *item->expr, {}, context);
            bad |= expr.bad() || indexExpr->bad();

            indexSetters.push_back(IndexSetter{indexExpr, &expr});
        }
    }

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, std::span<const MemberSetter>{}, std::span<const TypeSetter>{},
        indexSetters.copy(comp), defaultSetter, std::span<const Expression*>{}, sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

void StructuredAssignmentPatternExpression::serializeTo(ASTSerializer& serializer) const {
    if (defaultSetter)
        serializer.write("defaultSetter", *defaultSetter);

    if (!memberSetters.empty()) {
        serializer.startArray("memberSetters");
        for (auto& setter : memberSetters) {
            serializer.startObject();
            serializer.writeLink("member", *setter.member);
            serializer.write("expr", *setter.expr);
            serializer.endObject();
        }
        serializer.endArray();
    }

    if (!typeSetters.empty()) {
        serializer.startArray("typeSetters");
        for (auto& setter : typeSetters) {
            serializer.startObject();
            serializer.write("type", *setter.type);
            serializer.write("expr", *setter.expr);
            serializer.endObject();
        }
        serializer.endArray();
    }

    if (!indexSetters.empty()) {
        serializer.startArray("indexSetters");
        for (auto& setter : indexSetters) {
            serializer.startObject();
            serializer.write("index", *setter.index);
            serializer.write("expr", *setter.expr);
            serializer.endObject();
        }
        serializer.endArray();
    }
}

const Expression& ReplicatedAssignmentPatternExpression::bindReplCount(
    Compilation& comp, const ExpressionSyntax& syntax, const ASTContext& context, size_t& count) {

    const Expression& expr = bind(syntax, context);
    std::optional<int32_t> c = context.evalInteger(expr);
    if (!context.requireGtZero(c, expr.sourceRange))
        return badExpr(comp, &expr);

    count = size_t(*c);
    return expr;
}

Expression& ReplicatedAssignmentPatternExpression::forStruct(
    Compilation& comp, const ReplicatedAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Scope& structScope, SourceRange sourceRange) {

    size_t count = 0;
    auto& countExpr = bindReplCount(comp, *syntax.countExpr, context, count);
    if (countExpr.bad())
        return badExpr(comp, nullptr);

    SmallVector<const Type*> types;
    for (auto& field : structScope.membersOfType<FieldSymbol>())
        types.push_back(&field.getType());

    if (types.size() != syntax.items.size() * count) {
        auto& diag = context.addDiag(diag::WrongNumberAssignmentPatterns, sourceRange);
        diag << type << types.size() << syntax.items.size() * count;
        return badExpr(comp, nullptr);
    }

    bool bad = false;
    size_t index = 0;
    SmallVector<const Expression*> elems;
    for (auto item : syntax.items) {
        auto& expr = Expression::bindRValue(*types[index++], *item, {}, context);
        elems.push_back(&expr);
        bad |= expr.bad();
    }

    auto result = comp.emplace<ReplicatedAssignmentPatternExpression>(type, countExpr,
                                                                      elems.copy(comp),
                                                                      sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& ReplicatedAssignmentPatternExpression::forFixedArray(
    Compilation& comp, const ReplicatedAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, bitwidth_t numElements, SourceRange sourceRange) {

    size_t count = 0;
    auto& countExpr = bindReplCount(comp, *syntax.countExpr, context, count);
    if (countExpr.bad())
        return badExpr(comp, nullptr);

    bool bad = false;
    auto elems = bindExpressionList(type, elementType, count, numElements, syntax.items, context,
                                    sourceRange, bad);

    auto result = comp.emplace<ReplicatedAssignmentPatternExpression>(type, countExpr, elems,
                                                                      sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& ReplicatedAssignmentPatternExpression::forDynamicArray(
    Compilation& comp, const ReplicatedAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    size_t count = 0;
    auto& countExpr = bindReplCount(comp, *syntax.countExpr, context, count);
    if (countExpr.bad())
        return badExpr(comp, nullptr);

    bool bad = false;
    auto elems = bindExpressionList(type, elementType, count, 0, syntax.items, context, sourceRange,
                                    bad);

    auto result = comp.emplace<ReplicatedAssignmentPatternExpression>(type, countExpr, elems,
                                                                      sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

void ReplicatedAssignmentPatternExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("count", count());
    AssignmentPatternExpressionBase::serializeTo(serializer);
}

} // namespace slang::ast
