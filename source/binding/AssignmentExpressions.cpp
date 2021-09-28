//------------------------------------------------------------------------------
// AssignmentExpressions.cpp
// Definitions for assignment-related expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/AssignmentExpressions.h"

#include "slang/binding/Bitstream.h"
#include "slang/binding/CallExpression.h"
#include "slang/binding/LiteralExpressions.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/binding/OperatorExpressions.h"
#include "slang/binding/SelectExpressions.h"
#include "slang/binding/TimingControl.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/AllTypes.h"

namespace {

using namespace slang;

bool checkEnumInitializer(const BindContext& context, const Type& lt, const Expression& rhs) {
    // [6.19] says that the initializer for an enum value must be an integer expression that
    // does not truncate any bits. Furthermore, if a sized literal constant is used, it must
    // be sized exactly to the size of the enum base type.
    const Type& rt = *rhs.type;
    if (!rt.isIntegral()) {
        context.addDiag(diag::ValueMustBeIntegral, rhs.sourceRange);
        return false;
    }

    if (lt.getBitWidth() != rt.getBitWidth() && rhs.kind == ExpressionKind::IntegerLiteral &&
        !rhs.as<IntegerLiteral>().isDeclaredUnsized) {
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

Expression* Expression::tryConnectPortArray(const BindContext& context, const Type& portType,
                                            Expression& expr, const InstanceSymbolBase& instance) {
    // This lambda is shared code for reporting an error and returning an invalid expression.
    auto& comp = context.getCompilation();
    auto bad = [&]() {
        auto& diag = context.addDiag(diag::PortConnArrayMismatch, expr.sourceRange);
        diag << *expr.type << portType;

        string_view name = instance.getArrayName();
        if (name.empty())
            diag << "<unknown>"sv;
        else {
            diag << name;
            if (instance.location)
                diag << SourceRange{ instance.location, instance.location + name.length() };
        }

        return &badExpr(comp, &expr);
    };

    // Collect all of the dimensions of the instance array that owns the provided instance, ex:
    // MyMod instArray [3][4] (.conn(vec));
    //                 ^~~~~~  // these guys
    SmallVectorSized<ConstantRange, 8> instanceDimVec;
    instance.getArrayDimensions(instanceDimVec);

    span<const ConstantRange> instanceDims = instanceDimVec;
    span<const int32_t> arrayPath = instance.arrayPath;

    // If the connection has any unpacked dimensions, match them up with
    // the leading instance dimensions now.
    Expression* result = &expr;
    const Type* ct = &expr.type->getCanonicalType();
    if (ct->kind == SymbolKind::FixedSizeUnpackedArrayType) {
        SmallVectorSized<ConstantRange, 8> unpackedDimVec;
        const FixedSizeUnpackedArrayType* curr = &ct->as<FixedSizeUnpackedArrayType>();
        while (true) {
            unpackedDimVec.append(curr->range);
            ct = &curr->elementType.getCanonicalType();
            if (ct->kind != SymbolKind::FixedSizeUnpackedArrayType)
                break;

            curr = &ct->as<FixedSizeUnpackedArrayType>();
        }

        // Select each element of the connection array based on the index of
        // the instance in the instance array path. Elements get matched
        // left index to left index.
        span<const ConstantRange> unpackedDims = unpackedDimVec;
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
            if (!portType.isEquivalent(
                    FixedSizeUnpackedArrayType::fromDims(comp, *ct, unpackedDims))) {
                return bad();
            }

            ASSERT(instanceDims.empty());
            ASSERT(arrayPath.empty());
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
    if (numInstances * portWidth != ct->getBitWidth())
        return bad();

    // Convert the port expression to a simple bit vector so that we can select
    // bit ranges from it -- the range select expression works on the declared
    // range of the packed array so a multidimensional wouldn't work correctly
    // without this conversion.
    result = &ConversionExpression::makeImplicit(
        context, comp.getType(numInstances * portWidth, result->type->getIntegralFlags()),
        ConversionKind::Implicit, *result, result->sourceRange.start());

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
    ConstantRange range{ offset + width - 1, offset };
    return &RangeSelectExpression::fromConstant(comp, *result, range, context);
}

bool Expression::isImplicitlyAssignableTo(const Type& targetType) const {
    return targetType.isAssignmentCompatible(*type) ||
           ((targetType.isString() || targetType.isByteArray()) && isImplicitString()) ||
           (targetType.isEnum() && isSameEnum(*this, targetType));
}

Expression& Expression::convertAssignment(const BindContext& context, const Type& type,
                                          Expression& expr, SourceLocation location,
                                          Expression** lhsExpr) {
    if (expr.bad())
        return expr;

    Compilation& compilation = context.getCompilation();
    if (type.isError())
        return badExpr(compilation, &expr);

    Expression* result = &expr;
    const Type* rt = expr.type;
    if (type.isEquivalent(*rt)) {
        selfDetermined(context, result);
        return *result;
    }

    // If this is a port connection to an array of instances, check if the provided
    // expression represents an array that should be sliced on a per-instance basis.
    if (context.instance && !context.instance->arrayPath.empty()) {
        // If the connection is already of the right size and simply differs in
        // terms of four-statedness or signedness, don't bother trying to slice
        // out the connection.
        if (type.getBitWidth() != rt->getBitWidth() || !type.isAssignmentCompatible(*rt)) {
            // If we have an lhsExpr here, this is an output (or inout) port being connected.
            // We need to pass the lhs in as the expression to be connected, since we can't
            // slice the port side. If lhsExpr is null, this is an input port and we should
            // slice the incoming expression as an rvalue.
            if (lhsExpr) {
                Expression* conn = tryConnectPortArray(context, *rt, **lhsExpr, *context.instance);
                if (conn) {
                    selfDetermined(context, conn);
                    *lhsExpr = conn;

                    selfDetermined(context, result);
                    return *result;
                }
            }
            else {
                Expression* conn = tryConnectPortArray(context, type, expr, *context.instance);
                if (conn) {
                    selfDetermined(context, conn);
                    return *conn;
                }
            }
        }
    }

    if (!type.isAssignmentCompatible(*rt)) {
        // String literals have a type of integer, but are allowed to implicitly convert to the
        // string type. See comments on isSameEnum for why that's here as well.
        if (expr.isImplicitlyAssignableTo(type)) {
            result = &ConversionExpression::makeImplicit(context, type, ConversionKind::Implicit,
                                                         *result, location);
            selfDetermined(context, result);
            return *result;
        }

        if (expr.kind == ExpressionKind::Streaming) {
            if (Bitstream::canBeSource(type, expr.as<StreamingConcatenationExpression>(), location,
                                       context)) {
                // Add an implicit bit-stream casting otherwise types are not assignment compatible.
                // The size rule is not identical to explicit bit-stream casting so a different
                // ConversionKind is used.
                result = compilation.emplace<ConversionExpression>(
                    type, ConversionKind::StreamingConcat, *result, result->sourceRange);
                selfDetermined(context, result);
                return *result;
            }
            return badExpr(compilation, &expr);
        }

        DiagCode code = type.isCastCompatible(*rt) || type.isBitstreamCastable(*rt)
                            ? diag::NoImplicitConversion
                            : diag::BadAssignment;
        auto& diag = context.addDiag(code, location);
        diag << *rt << type;
        if (lhsExpr)
            diag << (*lhsExpr)->sourceRange;

        diag << expr.sourceRange;
        return badExpr(compilation, &expr);
    }

    if (type.isNumeric() && rt->isNumeric()) {
        if ((context.flags & BindFlags::EnumInitializer) != 0 &&
            !checkEnumInitializer(context, type, *result)) {

            return badExpr(compilation, &expr);
        }

        // The "signednessFromRt" flag is important here; only the width of the lhs is
        // propagated down to operands, not the sign flag. Once the expression is appropriately
        // sized, the makeImplicit call down below will convert the sign for us.
        rt = binaryOperatorType(compilation, &type, rt, false, /* signednessFromRt */ true);
        bool expanding = type.isEquivalent(*rt);
        if (expanding)
            rt = &type;

        contextDetermined(context, result, *rt, location);
        if (expanding)
            return *result;

        // Do not convert (truncate) enum initializer so out of range value can be checked.
        if (context.flags.has(BindFlags::EnumInitializer)) {
            selfDetermined(context, result);
            return *result;
        }
    }

    return ConversionExpression::makeImplicit(context, type, ConversionKind::Implicit, *result,
                                              location);
}

Expression& AssignmentExpression::fromSyntax(Compilation& compilation,
                                             const BinaryExpressionSyntax& syntax,
                                             const BindContext& context) {
    bool isNonBlocking = syntax.kind == SyntaxKind::NonblockingAssignmentExpression;

    if (isNonBlocking && context.flags.has(BindFlags::Final)) {
        context.addDiag(diag::NonblockingInFinal, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    if (!context.flags.has(BindFlags::AssignmentAllowed)) {
        if (!context.flags.has(BindFlags::NonProcedural) &&
            !context.flags.has(BindFlags::AssignmentDisallowed)) {
            context.addDiag(diag::AssignmentRequiresParens, syntax.sourceRange());
        }
        else {
            context.addDiag(diag::AssignmentNotAllowed, syntax.sourceRange());
        }
        return badExpr(compilation, nullptr);
    }

    bitmask<BindFlags> extraFlags = BindFlags::None;
    optional<BinaryOperator> op;
    if (syntax.kind != SyntaxKind::AssignmentExpression &&
        syntax.kind != SyntaxKind::NonblockingAssignmentExpression) {
        op = getBinaryOperator(syntax.kind);
    }
    else {
        extraFlags |= BindFlags::StreamingAllowed;
    }

    const ExpressionSyntax* rightExpr = syntax.right;

    // If we're in a top-level statement, check for an intra-assignment timing control.
    // Otherwise, we'll let this fall through to the default handler which will issue an error.
    const TimingControl* timingControl = nullptr;
    if (context.flags.has(BindFlags::TopLevelStatement) &&
        rightExpr->kind == SyntaxKind::TimingControlExpression) {

        BindContext timingCtx = context;
        timingCtx.flags |= BindFlags::LValue;
        if (isNonBlocking)
            timingCtx.flags |= BindFlags::NonBlockingTimingControl;

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
            Expression* rhs = &selfDetermined(compilation, *rightExpr, context);
            if (rhs->bad())
                return badExpr(compilation, rhs);

            auto lhs = &create(compilation, *syntax.left, context, BindFlags::LValue, rhs->type);
            selfDetermined(context, lhs);

            return fromComponents(compilation, op, isNonBlocking, *lhs, *rhs,
                                  syntax.operatorToken.location(), timingControl,
                                  syntax.sourceRange(), context);
        }
    }

    auto& lhs = selfDetermined(compilation, *syntax.left, context, extraFlags | BindFlags::LValue);

    Expression* rhs = nullptr;
    if (lhs.type->isVirtualInterface())
        rhs = tryBindInterfaceRef(context, *rightExpr, *lhs.type);

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

    return fromComponents(compilation, op, isNonBlocking, lhs, *rhs,
                          syntax.operatorToken.location(), timingControl, syntax.sourceRange(),
                          context);
}

Expression& AssignmentExpression::fromComponents(
    Compilation& compilation, optional<BinaryOperator> op, bool nonBlocking, Expression& lhs,
    Expression& rhs, SourceLocation assignLoc, const TimingControl* timingControl,
    SourceRange sourceRange, const BindContext& context) {

    auto result = compilation.emplace<AssignmentExpression>(op, nonBlocking, *lhs.type, lhs, rhs,
                                                            timingControl, sourceRange);
    if (lhs.bad() || rhs.bad())
        return badExpr(compilation, result);

    // Make sure we can actually assign to the thing on the lhs.
    if (!lhs.verifyAssignable(context, assignLoc, nonBlocking))
        return badExpr(compilation, result);

    if (lhs.kind == ExpressionKind::Streaming) {
        if (!Bitstream::canBeTarget(lhs.as<StreamingConcatenationExpression>(), rhs, assignLoc,
                                    context)) {
            return badExpr(compilation, result);
        }
        return *result;
    }

    // If this is a compound assignment operator create a binary expression that will
    // apply the operator for us on the right hand side.
    if (op) {
        auto lvalRef = compilation.emplace<LValueReferenceExpression>(*lhs.type, lhs.sourceRange);
        result->right_ = &BinaryExpression::fromComponents(*lvalRef, *result->right_, *op,
                                                           assignLoc, sourceRange, context);
    }

    result->right_ =
        &convertAssignment(context, *lhs.type, *result->right_, assignLoc, &result->left_);
    if (result->right_->bad())
        return badExpr(compilation, result);

    if (timingControl) {
        // Cycle delays are only allowed on clock vars, and clock vars
        // cannot use any timing control other than cycle delays.
        if (auto sym = lhs.getSymbolReference(); sym && sym->kind == SymbolKind::ClockVar) {
            if (timingControl->kind != TimingControlKind::CycleDelay) {
                ASSERT(timingControl->syntax);
                context.addDiag(diag::ClockVarBadTiming, timingControl->syntax->sourceRange());
            }
        }
        else if (timingControl->kind == TimingControlKind::CycleDelay) {
            ASSERT(timingControl->syntax);
            context.addDiag(diag::CycleDelayNonClock, timingControl->syntax->sourceRange());
        }
    }

    return *result;
}

ConstantValue AssignmentExpression::evalImpl(EvalContext& context) const {
    if (!context.isScriptEval() && timingControl)
        return nullptr;

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

bool AssignmentExpression::verifyConstantImpl(EvalContext& context) const {
    if (!context.isScriptEval() && timingControl) {
        context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
        return false;
    }

    return left().verifyConstant(context) && right().verifyConstant(context);
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

Expression& ConversionExpression::fromSyntax(Compilation& compilation,
                                             const CastExpressionSyntax& syntax,
                                             const BindContext& context) {
    auto& targetExpr = bind(*syntax.left, context, BindFlags::AllowDataType | BindFlags::Constant);
    auto& operand =
        selfDetermined(compilation, *syntax.right, context, BindFlags::StreamingAllowed);

    const auto* type = &compilation.getErrorType();
    auto result = [&](ConversionKind cast = ConversionKind::Explicit) {
        return compilation.emplace<ConversionExpression>(*type, cast, operand,
                                                         syntax.sourceRange());
    };

    if (targetExpr.bad() || operand.bad())
        return badExpr(compilation, result());

    if (targetExpr.kind == ExpressionKind::DataType) {
        type = targetExpr.type;
        if (!type->isSimpleType() && !type->isError() && !type->isString() &&
            syntax.left->kind != SyntaxKind::TypeReference) {
            context.addDiag(diag::BadCastType, targetExpr.sourceRange) << *type;
            return badExpr(compilation, result());
        }
    }
    else {
        auto val = context.evalInteger(targetExpr);
        if (!val || !context.requireGtZero(val, targetExpr.sourceRange))
            return badExpr(compilation, result());

        bitwidth_t width = bitwidth_t(*val);
        if (!context.requireValidBitWidth(width, targetExpr.sourceRange))
            return badExpr(compilation, result());

        if (!operand.type->isIntegral()) {
            auto& diag = context.addDiag(diag::BadIntegerCast, syntax.apostrophe.location());
            diag << *operand.type;
            diag << targetExpr.sourceRange << operand.sourceRange;
            return badExpr(compilation, result());
        }

        type = &compilation.getType(width, operand.type->getIntegralFlags());
    }

    if (!type->isCastCompatible(*operand.type)) {
        if (operand.kind == ExpressionKind::Streaming) {
            if (!Bitstream::isBitstreamCast(*type,
                                            operand.as<StreamingConcatenationExpression>())) {
                auto& diag = context.addDiag(diag::BadStreamCast, syntax.apostrophe.location());
                diag << *type;
                diag << targetExpr.sourceRange << operand.sourceRange;
                return badExpr(compilation, result());
            }
        }
        else if (!type->isBitstreamCastable(*operand.type)) {
            auto& diag = context.addDiag(diag::BadConversion, syntax.apostrophe.location());
            diag << *operand.type << *type;
            diag << targetExpr.sourceRange << operand.sourceRange;
            return badExpr(compilation, result());
        }

        return *result(ConversionKind::BitstreamCast);
    }

    return *result();
}

Expression& ConversionExpression::fromSyntax(Compilation& compilation,
                                             const SignedCastExpressionSyntax& syntax,
                                             const BindContext& context) {
    auto& operand = selfDetermined(compilation, *syntax.inner, context);
    auto result = compilation.emplace<ConversionExpression>(
        compilation.getErrorType(), ConversionKind::Explicit, operand, syntax.sourceRange());
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

static void checkImplicitConversions(const BindContext& context, const Type& targetType,
                                     const Expression& op, SourceLocation loc) {
    auto isStructUnionEnum = [](const Type& t) {
        return t.kind == SymbolKind::PackedStructType || t.kind == SymbolKind::PackedUnionType ||
               t.kind == SymbolKind::EnumType;
    };

    const Type& sourceType = *op.type;
    const Type& lt = targetType.getCanonicalType();
    const Type& rt = sourceType.getCanonicalType();
    if (lt.isIntegral() && rt.isIntegral()) {
        // Warn for conversions between different enums/structs/unions.
        if (isStructUnionEnum(lt) && isStructUnionEnum(rt) && !lt.isMatching(rt)) {
            context.addDiag(diag::ImplicitConvert, loc)
                << sourceType << targetType << op.sourceRange;
            return;
        }

        // Warn for implicit assignments between integral types of differing widths.
        bitwidth_t targetWidth = lt.getBitWidth();
        bitwidth_t actualWidth = rt.getBitWidth();
        if (targetWidth == actualWidth || context.flags.has(BindFlags::Constant))
            return;

        // Before we go and issue this warning, weed out false positives by
        // recomputing the width of the expression, with all constants sized
        // to the minimum width necessary to represent them. Otherwise, even
        // code as simple as this will result in a warning:
        //    logic [3:0] a = 1;
        optional<bitwidth_t> effective = op.getEffectiveWidth();
        if (!effective)
            return;

        // Now that we know the effective width, compare it to the expression's
        // actual width. We don't warn if the target is anywhere in between the
        // effective and the actual width.
        ASSERT(effective <= actualWidth);
        if (targetWidth < effective || targetWidth > actualWidth) {
            // Final check to rule out false positives: try to eval as a constant.
            // We'll ignore any constants, because as described above they
            // will get their own more fine grained warning later during eval.
            if (!context.tryEval(op)) {
                DiagCode code = targetWidth < effective ? diag::WidthTruncate : diag::WidthExpand;
                context.addDiag(code, loc) << actualWidth << targetWidth << op.sourceRange;
            }
        }
    }
}

Expression& ConversionExpression::makeImplicit(const BindContext& context, const Type& targetType,
                                               ConversionKind conversionKind, Expression& expr,
                                               SourceLocation loc) {
    ASSERT(expr.isImplicitlyAssignableTo(targetType));

    Expression* op = &expr;
    selfDetermined(context, op);

    // Check if we should issue any warnings for implicit integer conversions.
    // Note that this does not apply to propagated conversions, as those almost
    // always do the right thing and the warnings would be very noisy.
    if (conversionKind == ConversionKind::Implicit && !context.inUnevaluatedBranch())
        checkImplicitConversions(context, targetType, *op, loc);

    return *context.getCompilation().emplace<ConversionExpression>(targetType, conversionKind, *op,
                                                                   op->sourceRange);
}

ConstantValue ConversionExpression::evalImpl(EvalContext& context) const {
    return convert(context, *operand().type, *type, sourceRange, operand().eval(context),
                   conversionKind);
}

ConstantValue ConversionExpression::convert(EvalContext& context, const Type& from, const Type& to,
                                            SourceRange sourceRange, ConstantValue&& value,
                                            ConversionKind conversionKind) {
    if (!value)
        return nullptr;

    if (from.isMatching(to))
        return std::move(value);

    if (conversionKind == ConversionKind::BitstreamCast ||
        conversionKind == ConversionKind::StreamingConcat) {
        return Bitstream::evaluateCast(to, std::move(value), sourceRange, context,
                                       conversionKind == ConversionKind::StreamingConcat);
    }

    if (to.isIntegral()) {
        // [11.8.2] last bullet says: the operand shall be sign-extended only if the propagated type
        // is signed. It is different from [11.8.3] ConstantValue::convertToInt uses.
        // ConversionKind::Propagated marked in Expression::PropagationVisitor
        if (conversionKind == ConversionKind::Propagated && value.isInteger())
            value.integer().setSigned(to.isSigned());
        return value.convertToInt(to.getBitWidth(), to.isSigned(), to.isFourState());
    }

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

    if (to.isUnpackedArray() && from.isUnpackedArray()) {
        // Conversion to a dynamic array just resizes. Conversion to a fixed array
        // must have the same number of elements in the source.
        ASSERT(!to.hasFixedRange() || !from.hasFixedRange());
        if (to.hasFixedRange()) {
            size_t size = value.size();
            if (size != to.getFixedRange().width()) {
                context.addDiag(diag::ConstEvalDynamicToFixedSize, sourceRange)
                    << from << size << to;
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

    THROW_UNREACHABLE;
}

bool ConversionExpression::verifyConstantImpl(EvalContext& context) const {
    return operand().verifyConstant(context);
}

optional<bitwidth_t> ConversionExpression::getEffectiveWidthImpl() const {
    if (isImplicit())
        return operand().getEffectiveWidth();
    return type->getBitWidth();
}

void ConversionExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("operand", operand());
}

Expression& NewArrayExpression::fromSyntax(Compilation& compilation,
                                           const NewArrayExpressionSyntax& syntax,
                                           const BindContext& context,
                                           const Type* assignmentTarget) {
    if (!assignmentTarget ||
        assignmentTarget->getCanonicalType().kind != SymbolKind::DynamicArrayType) {
        context.addDiag(diag::NewArrayTarget, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    auto& sizeExpr = selfDetermined(compilation, *syntax.sizeExpr, context);
    const Expression* initExpr = nullptr;
    if (syntax.initializer) {
        initExpr = &bindRValue(*assignmentTarget, *syntax.initializer->expression,
                               syntax.initializer->getFirstToken().location(), context);
    }

    auto result = compilation.emplace<NewArrayExpression>(*assignmentTarget, sizeExpr, initExpr,
                                                          syntax.sourceRange());
    if (sizeExpr.bad() || (initExpr && initExpr->bad()))
        return badExpr(compilation, result);

    if (!sizeExpr.type->isIntegral()) {
        context.addDiag(diag::ExprMustBeIntegral, sizeExpr.sourceRange) << *sizeExpr.type;
        return badExpr(compilation, result);
    }

    return *result;
}

ConstantValue NewArrayExpression::evalImpl(EvalContext& context) const {
    ConstantValue sz = sizeExpr().eval(context);
    if (!sz)
        return nullptr;

    optional<int64_t> size = sz.integer().as<int64_t>();
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

bool NewArrayExpression::verifyConstantImpl(EvalContext& context) const {
    return sizeExpr().verifyConstant(context) &&
           (!initExpr() || initExpr()->verifyConstant(context));
}

void NewArrayExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("sizeExpr", sizeExpr());
    if (initExpr())
        serializer.write("initExpr", *initExpr());
}

Expression& NewClassExpression::fromSyntax(Compilation& compilation,
                                           const NewClassExpressionSyntax& syntax,
                                           const BindContext& context,
                                           const Type* assignmentTarget) {
    // If the new expression is typed, look up that type as the target.
    // Otherwise, the target must come from the expression context.
    bool isSuperClass = false;
    const ClassType* classType = nullptr;
    if (syntax.scopedNew->kind == SyntaxKind::ConstructorName) {
        if (!assignmentTarget || !assignmentTarget->isClass()) {
            if (!assignmentTarget || !assignmentTarget->isError())
                context.addDiag(diag::NewClassTarget, syntax.sourceRange());
            return badExpr(compilation, nullptr);
        }

        classType = &assignmentTarget->getCanonicalType().as<ClassType>();
    }
    else {
        auto& scoped = syntax.scopedNew->as<ScopedNameSyntax>();
        if (scoped.left->getLastToken().kind == TokenKind::SuperKeyword) {
            // This is a super.new invocation, so find the base class's
            // constructor. This is relative to our current context, not
            // any particular assignment target.
            auto [ct, _] = Lookup::getContainingClass(*context.scope);
            classType = ct;
            if (!classType) {
                // Parser already emitted an error for this case.
                return badExpr(compilation, nullptr);
            }

            auto base = classType->getBaseClass();
            if (!base) {
                context.addDiag(diag::SuperNoBase, syntax.scopedNew->sourceRange())
                    << classType->name;
                return badExpr(compilation, nullptr);
            }

            classType = &base->as<Type>().getCanonicalType().as<ClassType>();
            assignmentTarget = &compilation.getVoidType();
            isSuperClass = true;
        }
        else {
            auto& className = *syntax.scopedNew->as<ScopedNameSyntax>().left;
            classType = Lookup::findClass(className, context);
            if (!classType)
                return badExpr(compilation, nullptr);

            assignmentTarget = classType;
        }
    }

    if (!isSuperClass && classType->isAbstract) {
        context.addDiag(diag::NewVirtualClass, syntax.sourceRange()) << classType->name;
        return badExpr(compilation, nullptr);
    }

    if (!isSuperClass && classType->isInterface) {
        context.addDiag(diag::NewInterfaceClass, syntax.sourceRange()) << classType->name;
        return badExpr(compilation, nullptr);
    }

    SourceRange range = syntax.sourceRange();
    Expression* constructorCall = nullptr;
    if (auto constructor = classType->find("new")) {
        Lookup::ensureVisible(*constructor, context, range);
        constructorCall =
            &CallExpression::fromArgs(compilation, &constructor->as<SubroutineSymbol>(), nullptr,
                                      syntax.argList, range, context);
    }
    else if (syntax.argList && !syntax.argList->parameters.empty()) {
        auto& diag = context.addDiag(diag::TooManyArguments, syntax.argList->sourceRange());
        diag << "new"sv;
        diag << 0;
        diag << syntax.argList->parameters.size();
    }

    auto result = compilation.emplace<NewClassExpression>(*assignmentTarget, constructorCall,
                                                          isSuperClass, range);
    return *result;
}

ConstantValue NewClassExpression::evalImpl(EvalContext&) const {
    return nullptr;
}

bool NewClassExpression::verifyConstantImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalClassType, sourceRange);
    return false;
}

void NewClassExpression::serializeTo(ASTSerializer& serializer) const {
    if (constructorCall())
        serializer.write("constructorCall", *constructorCall());
}

} // namespace slang
