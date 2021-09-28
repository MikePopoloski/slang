//------------------------------------------------------------------------------
// SelectExpressions.cpp
// Definitions for selection expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SelectExpressions.h"

#include "slang/binding/CallExpression.h"
#include "slang/binding/LiteralExpressions.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/AllTypes.h"

namespace {

using namespace slang;

const Type& getIndexedType(Compilation& compilation, const BindContext& context,
                           const Type& valueType, SourceRange exprRange, SourceRange valueRange,
                           bool isRangeSelect) {
    const Type& ct = valueType.getCanonicalType();
    if (ct.isArray()) {
        return *ct.getArrayElementType();
    }
    else if (ct.kind == SymbolKind::StringType && !isRangeSelect) {
        return compilation.getByteType();
    }
    else if (!ct.isIntegral()) {
        auto& diag = context.addDiag(diag::BadIndexExpression, exprRange);
        diag << valueRange;
        diag << valueType;
        return compilation.getErrorType();
    }
    else if (ct.isScalar()) {
        auto& diag = context.addDiag(diag::CannotIndexScalar, exprRange);
        diag << valueRange;
        return compilation.getErrorType();
    }
    else if (ct.isFourState()) {
        return compilation.getLogicType();
    }
    else {
        return compilation.getBitType();
    }
}

optional<ConstantRange> getFixedIndex(const ConstantValue& cs, const Type& valueType,
                                      const Type& resultType, EvalContext& context,
                                      SourceRange sourceRange) {
    optional<int32_t> index = cs.integer().as<int32_t>();
    ConstantRange range = valueType.getFixedRange();
    if (!index || !range.containsPoint(*index)) {
        context.addDiag(diag::ConstEvalArrayIndexInvalid, sourceRange) << cs << valueType;
        return std::nullopt;
    }

    if (valueType.isUnpackedArray()) {
        // Unpacked arrays are stored reversed in memory, so reverse the range here.
        range = range.reverse();
        int32_t i = range.translateIndex(*index);
        return ConstantRange{ i, i };
    }

    // For packed arrays, we're selecting bit ranges, not necessarily single bits,
    // so multiply out by the width of each element.
    int32_t width = (int32_t)resultType.getBitWidth();
    int32_t i = range.translateIndex(*index) * width;
    return ConstantRange{ i + width - 1, i };
}

optional<int32_t> getDynamicIndex(const ConstantValue& cs, const ConstantValue& cv,
                                  const Type& valueType, EvalContext& context,
                                  SourceRange sourceRange) {
    optional<int32_t> index = cs.integer().as<int32_t>();
    if (valueType.isString()) {
        const std::string& str = cv.str();
        if (!index || *index < 0 || size_t(*index) >= str.size()) {
            context.addDiag(diag::ConstEvalStringIndexInvalid, sourceRange) << cs << str.size();
            return std::nullopt;
        }

        return index;
    }

    // For dynamic arrays and queues, elements out of bounds only issue a warning.
    size_t maxIndex = cv.size();
    if (cv.isQueue())
        maxIndex++;

    if (!index || *index < 0 || size_t(*index) >= maxIndex) {
        context.addDiag(diag::ConstEvalDynamicArrayIndex, sourceRange)
            << cs << valueType << maxIndex;

        // Return a sentinel value (which is never valid as a dynamic array index).
        return -1;
    }

    return index;
}

} // namespace

namespace slang {

static const ValueSymbol* getValueFrom(const Expression& expr) {
    if (expr.kind == ExpressionKind::NamedValue)
        return &expr.as<NamedValueExpression>().symbol;
    if (expr.kind == ExpressionKind::HierarchicalValue)
        return &expr.as<HierarchicalValueExpression>().symbol;
    return nullptr;
}

static void checkForVectoredSelect(const Expression& value, SourceRange range,
                                   const BindContext& context) {
    if (auto sym = getValueFrom(value); sym && sym->kind == SymbolKind::Net &&
                                        sym->as<NetSymbol>().expansionHint == NetSymbol::Vectored) {
        auto& diag = context.addDiag(diag::SelectOfVectoredNet, range);
        diag.addNote(diag::NoteDeclarationHere, sym->location);
    }
}

Expression& ElementSelectExpression::fromSyntax(Compilation& compilation, Expression& value,
                                                const ExpressionSyntax& syntax,
                                                SourceRange fullRange, const BindContext& context) {
    if (value.bad())
        return badExpr(compilation, nullptr);

    // Selects of vectored nets are disallowed.
    checkForVectoredSelect(value, fullRange, context);

    const Type& valueType = *value.type;
    const Type& resultType = getIndexedType(compilation, context, valueType, syntax.sourceRange(),
                                            value.sourceRange, false);

    // If this is an associative array with a specific index target, we need to bind
    // as an rvalue to get the right conversion applied.
    const Expression* selector = nullptr;
    if (valueType.isAssociativeArray()) {
        auto indexType = valueType.getAssociativeIndexType();
        if (indexType)
            selector = &bindRValue(*indexType, syntax, syntax.getFirstToken().location(), context);
    }

    if (!selector) {
        bitmask<BindFlags> flags;
        if (valueType.isQueue())
            flags = BindFlags::AllowUnboundedLiteral | BindFlags::AllowUnboundedLiteralArithmetic;

        selector = &selfDetermined(compilation, syntax, context, flags);
        if (!selector->bad() && !selector->type->isIntegral() && !selector->type->isUnbounded()) {
            context.addDiag(diag::ExprMustBeIntegral, selector->sourceRange) << *selector->type;
            return badExpr(compilation, nullptr);
        }
    }

    auto result =
        compilation.emplace<ElementSelectExpression>(resultType, value, *selector, fullRange);
    if (selector->bad() || result->bad())
        return badExpr(compilation, result);

    // If the selector is constant, and the underlying type has a fixed range,
    // we can do checking at compile time that it's within bounds.
    // Only do that if we're not in an unevaluated conditional branch.
    if (valueType.hasFixedRange()) {
        ConstantValue selVal;
        if (!context.inUnevaluatedBranch() && (selVal = context.tryEval(*selector))) {
            optional<int32_t> index = selVal.integer().as<int32_t>();
            if (!index || !valueType.getFixedRange().containsPoint(*index)) {
                auto& diag = context.addDiag(diag::IndexValueInvalid, selector->sourceRange);
                diag << selVal;
                diag << *value.type;
                return badExpr(compilation, result);
            }
        }
    }
    else if (context.flags.has(BindFlags::NonProcedural)) {
        context.addDiag(diag::DynamicNotProcedural, fullRange);
        return badExpr(compilation, result);
    }

    return *result;
}

Expression& ElementSelectExpression::fromConstant(Compilation& compilation, Expression& value,
                                                  int32_t index, const BindContext& context) {
    Expression* indexExpr = &IntegerLiteral::fromConstant(compilation, index);
    selfDetermined(context, indexExpr);

    const Type& resultType = getIndexedType(compilation, context, *value.type,
                                            indexExpr->sourceRange, value.sourceRange, false);

    auto result = compilation.emplace<ElementSelectExpression>(resultType, value, *indexExpr,
                                                               value.sourceRange);
    if (value.bad() || indexExpr->bad() || result->bad())
        return badExpr(compilation, result);

    return *result;
}

ConstantValue ElementSelectExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    if (!cv)
        return nullptr;

    auto prevQ = context.getQueueTarget();
    if (cv.isQueue())
        context.setQueueTarget(&cv);

    ConstantValue cs = selector().eval(context);

    context.setQueueTarget(prevQ);
    if (!cs)
        return nullptr;

    // Handling for packed and unpacked arrays, all integer types.
    const Type& valType = *value().type;
    if (valType.hasFixedRange()) {
        auto range = getFixedIndex(cs, valType, *type, context, sourceRange);
        if (!range)
            return nullptr;

        // For fixed types, we know we will always be in range, so just do the selection.
        if (valType.isUnpackedArray())
            return cv.elements()[size_t(range->left)];
        else
            return cv.integer().slice(range->left, range->right);
    }

    // Handling for associative arrays.
    if (valType.isAssociativeArray()) {
        if (cs.hasUnknown()) {
            context.addDiag(diag::ConstEvalAssociativeIndexInvalid, selector().sourceRange) << cs;
            return nullptr;
        }

        auto& map = *cv.map();
        if (auto it = map.find(cs); it != map.end())
            return it->second;

        // If there is a user specified default, return that without warning.
        if (map.defaultValue)
            return map.defaultValue;

        // Otherwise issue a warning and use the default default.
        context.addDiag(diag::ConstEvalAssociativeElementNotFound, selector().sourceRange)
            << value().sourceRange << cs;
        return type->getDefaultValue();
    }

    // Handling for strings, dynamic arrays, and queues.
    auto index = getDynamicIndex(cs, cv, valType, context, sourceRange);
    if (!index)
        return nullptr;

    if (valType.isString())
        return cv.getSlice(*index, *index, nullptr);

    // -1 is returned for dynamic array indices that are out of bounds.
    if (*index == -1)
        return type->getDefaultValue();

    return std::move(cv).at(size_t(*index));
}

LValue ElementSelectExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    if (!lval)
        return nullptr;

    auto prevQ = context.getQueueTarget();
    ConstantValue queueVal;
    if (value().type->isQueue()) {
        queueVal = lval.load();
        context.setQueueTarget(&queueVal);
    }

    ConstantValue cs = selector().eval(context);

    context.setQueueTarget(prevQ);
    if (!cs)
        return nullptr;

    // Handling for packed and unpacked arrays, all integer types.
    const Type& valType = *value().type;
    if (valType.hasFixedRange()) {
        auto range = getFixedIndex(cs, valType, *type, context, sourceRange);
        if (!range)
            return nullptr;

        // For fixed types, we know we will always be in range, so just do the selection.
        if (valType.isUnpackedArray())
            lval.addIndex(range->left, type->getDefaultValue());
        else
            lval.addBitSlice(*range);
        return lval;
    }

    // Handling for associative arrays.
    if (valType.isAssociativeArray()) {
        if (cs.hasUnknown()) {
            context.addDiag(diag::ConstEvalAssociativeIndexInvalid, selector().sourceRange) << cs;
            return nullptr;
        }

        lval.addArrayLookup(std::move(cs), type->getDefaultValue());
        return lval;
    }

    // Handling for strings, dynamic arrays, and queues.
    auto index = getDynamicIndex(cs, lval.load(), valType, context, sourceRange);
    if (!index)
        return nullptr;

    if (valType.isString()) {
        lval.addIndex(*index, nullptr);
    }
    else {
        // -1 is returned for dynamic array indices that are out of bounds.
        // LValue handles selecting elements out of bounds and ignores accesses to those locations.
        lval.addIndex(*index, type->getDefaultValue());
    }
    return lval;
}

bool ElementSelectExpression::verifyConstantImpl(EvalContext& context) const {
    return value().verifyConstant(context) && selector().verifyConstant(context);
}

void ElementSelectExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("value", value());
    serializer.write("selector", selector());
}

Expression& RangeSelectExpression::fromSyntax(Compilation& compilation, Expression& value,
                                              const RangeSelectSyntax& syntax,
                                              SourceRange fullRange, const BindContext& context) {
    // Left and right are either the extents of a part-select, in which case they must
    // both be constant, or the left hand side is the start and the right hand side is
    // the width of an indexed part select, in which case only the rhs need be constant.
    RangeSelectionKind selectionKind;
    switch (syntax.kind) {
        case SyntaxKind::SimpleRangeSelect:
            selectionKind = RangeSelectionKind::Simple;
            break;
        case SyntaxKind::AscendingRangeSelect:
            selectionKind = RangeSelectionKind::IndexedUp;
            break;
        case SyntaxKind::DescendingRangeSelect:
            selectionKind = RangeSelectionKind::IndexedDown;
            break;
        default:
            THROW_UNREACHABLE;
    }

    if (!value.bad() && value.type->isAssociativeArray()) {
        context.addDiag(diag::RangeSelectAssociative, fullRange);
        return badExpr(compilation, nullptr);
    }

    // Selection expressions don't need to be const if we're selecting from a queue.
    bool isQueue = value.type->isQueue();
    bool leftConst = !isQueue && selectionKind == RangeSelectionKind::Simple;
    bool rightConst = !isQueue;
    bitmask<BindFlags> extraFlags;
    if (isQueue)
        extraFlags = BindFlags::AllowUnboundedLiteral | BindFlags::AllowUnboundedLiteralArithmetic;

    auto& left = leftConst ? bind(*syntax.left, context, BindFlags::Constant | extraFlags)
                           : selfDetermined(compilation, *syntax.left, context, extraFlags);
    auto& right = rightConst ? bind(*syntax.right, context, BindFlags::Constant | extraFlags)
                             : selfDetermined(compilation, *syntax.right, context, extraFlags);

    auto result = compilation.emplace<RangeSelectExpression>(
        selectionKind, compilation.getErrorType(), value, left, right, fullRange);

    if (value.bad() || left.bad() || right.bad())
        return badExpr(compilation, result);

    if (!left.type->isIntegral() && !left.type->isUnbounded()) {
        context.addDiag(diag::ExprMustBeIntegral, left.sourceRange) << *left.type;
        return badExpr(compilation, result);
    }
    if (!right.type->isIntegral() && !right.type->isUnbounded()) {
        context.addDiag(diag::ExprMustBeIntegral, right.sourceRange) << *right.type;
        return badExpr(compilation, result);
    }

    const Type& valueType = *value.type;
    const Type& elementType = getIndexedType(compilation, context, valueType, syntax.sourceRange(),
                                             value.sourceRange, true);
    if (elementType.isError())
        return badExpr(compilation, result);

    // Selects of vectored nets are disallowed.
    checkForVectoredSelect(value, fullRange, context);

    if (!valueType.hasFixedRange() && context.flags.has(BindFlags::NonProcedural)) {
        context.addDiag(diag::DynamicNotProcedural, fullRange);
        return badExpr(compilation, result);
    }

    // If this is selecting from a queue, the result is always a queue.
    if (isQueue) {
        result->type = compilation.emplace<QueueType>(elementType, 0u);
        return *result;
    }

    // If not a queue, rhs must always be a constant integer.
    optional<int32_t> rv = context.evalInteger(right);
    if (!rv)
        return badExpr(compilation, result);

    // If the array type has a fixed range, validate that the range we're selecting is allowed.
    SourceRange errorRange{ left.sourceRange.start(), right.sourceRange.end() };
    if (valueType.hasFixedRange()) {
        ConstantRange selectionRange;
        ConstantRange valueRange = valueType.getFixedRange();

        // Helper function for validating the bounds of the selection.
        auto validateRange = [&](auto range) {
            if (!valueRange.containsPoint(range.left) || !valueRange.containsPoint(range.right)) {
                auto& diag = context.addDiag(diag::BadRangeExpression, errorRange);
                diag << range.left << range.right;
                diag << valueType;
                return false;
            }
            return true;
        };

        if (selectionKind == RangeSelectionKind::Simple) {
            optional<int32_t> lv = context.evalInteger(left);
            if (!lv)
                return badExpr(compilation, result);

            selectionRange = { *lv, *rv };
            if (selectionRange.isLittleEndian() != valueRange.isLittleEndian() &&
                selectionRange.width() > 1) {
                auto& diag = context.addDiag(diag::SelectEndianMismatch, errorRange);
                diag << valueType;
                return badExpr(compilation, result);
            }

            if (!context.inUnevaluatedBranch() && !validateRange(selectionRange))
                return badExpr(compilation, result);
        }
        else {
            if (!context.requireGtZero(rv, right.sourceRange))
                return badExpr(compilation, result);

            if (bitwidth_t(*rv) > valueRange.width()) {
                auto& diag = context.addDiag(diag::RangeWidthTooLarge, right.sourceRange);
                diag << *rv;
                diag << valueType;
                return badExpr(compilation, result);
            }

            // If the lhs is a known constant, we can check that now too.
            ConstantValue leftVal;
            if (!context.inUnevaluatedBranch() && (leftVal = context.tryEval(left))) {
                optional<int32_t> index = leftVal.integer().as<int32_t>();
                if (!index) {
                    auto& diag = context.addDiag(diag::IndexValueInvalid, left.sourceRange);
                    diag << leftVal;
                    diag << valueType;
                    return badExpr(compilation, result);
                }

                selectionRange =
                    ConstantRange::getIndexedRange(*index, *rv, valueRange.isLittleEndian(),
                                                   selectionKind == RangeSelectionKind::IndexedUp);

                if (!validateRange(selectionRange))
                    return badExpr(compilation, result);
            }
            else {
                // Otherwise, the resulting range will start with the fixed lower bound of the type.
                int32_t l = selectionKind == RangeSelectionKind::IndexedUp ? valueRange.lower()
                                                                           : valueRange.upper();
                selectionRange =
                    ConstantRange::getIndexedRange(l, *rv, valueRange.isLittleEndian(),
                                                   selectionKind == RangeSelectionKind::IndexedUp);
            }
        }

        // At this point, all expressions are good, ranges have been validated and
        // we know the final width of the selection, so pick the result type and we're done.
        if (valueType.isUnpackedArray()) {
            result->type =
                compilation.emplace<FixedSizeUnpackedArrayType>(elementType, selectionRange);
        }
        else {
            result->type = compilation.emplace<PackedArrayType>(elementType, selectionRange);
        }
    }
    else {
        // Otherwise, this is a dynamic array so we can't validate much. We should check that
        // the selection endianness is correct for simple ranges -- dynamic arrays only
        // permit big endian [0..N] ordering.
        ConstantRange selectionRange;
        if (selectionKind == RangeSelectionKind::Simple) {
            optional<int32_t> lv = context.evalInteger(left);
            if (!lv)
                return badExpr(compilation, result);

            selectionRange = { *lv, *rv };
            if (selectionRange.isLittleEndian() && selectionRange.width() > 1) {
                auto& diag = context.addDiag(diag::SelectEndianDynamic, errorRange);
                diag << selectionRange.left << selectionRange.right;
                diag << valueType;
                return badExpr(compilation, result);
            }
        }
        else {
            if (!context.requireGtZero(rv, right.sourceRange))
                return badExpr(compilation, result);

            selectionRange.left = 0;
            selectionRange.right = *rv - 1;
        }

        result->type = compilation.emplace<FixedSizeUnpackedArrayType>(elementType, selectionRange);
    }

    return *result;
}

Expression& RangeSelectExpression::fromConstant(Compilation& compilation, Expression& value,
                                                ConstantRange range, const BindContext& context) {
    Expression* left = &IntegerLiteral::fromConstant(compilation, range.left);
    selfDetermined(context, left);

    Expression* right = &IntegerLiteral::fromConstant(compilation, range.right);
    selfDetermined(context, right);

    auto result = compilation.emplace<RangeSelectExpression>(RangeSelectionKind::Simple,
                                                             compilation.getErrorType(), value,
                                                             *left, *right, value.sourceRange);
    if (value.bad() || left->bad() || right->bad())
        return badExpr(compilation, result);

    const Type& valueType = *value.type;
    const Type& elementType =
        getIndexedType(compilation, context, valueType, value.sourceRange, value.sourceRange, true);

    if (elementType.isError())
        return badExpr(compilation, result);

    // This method is only called on expressions with a fixed range type.
    ConstantRange valueRange = valueType.getFixedRange();
    ASSERT(range.isLittleEndian() == valueRange.isLittleEndian());
    ASSERT(valueType.hasFixedRange());

    if (valueType.isUnpackedArray())
        result->type = compilation.emplace<FixedSizeUnpackedArrayType>(elementType, range);
    else
        result->type = compilation.emplace<PackedArrayType>(elementType, range);

    return *result;
}

ConstantValue RangeSelectExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    if (!cv)
        return nullptr;

    auto prevQ = context.getQueueTarget();
    if (cv.isQueue())
        context.setQueueTarget(&cv);

    ConstantValue cl = left().eval(context);
    ConstantValue cr = right().eval(context);

    context.setQueueTarget(prevQ);
    if (!cl || !cr)
        return nullptr;

    if (value().type->hasFixedRange()) {
        optional<ConstantRange> range = getFixedRange(context, cl, cr);
        if (!range)
            return nullptr;

        return cv.getSlice(range->upper(), range->lower(), nullptr);
    }
    else {
        optional<ConstantRange> range = getDynamicRange(context, cl, cr, cv);
        if (!range)
            return nullptr;

        // If this is a queue, we didn't verify the endianness of the selection.
        // Check if it's reversed here and issue a warning if so.
        if (value().type->isQueue() && range->isLittleEndian() && range->left != range->right) {
            context.addDiag(diag::ConstEvalQueueRange, sourceRange) << range->left << range->right;
            return value().type->getDefaultValue();
        }

        return cv.getSlice(range->upper(), range->lower(),
                           type->getArrayElementType()->getDefaultValue());
    }
}

LValue RangeSelectExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    if (!lval)
        return nullptr;

    auto prevQ = context.getQueueTarget();
    ConstantValue queueVal;
    if (value().type->isQueue()) {
        queueVal = lval.load();
        context.setQueueTarget(&queueVal);
    }

    ConstantValue cl = left().eval(context);
    ConstantValue cr = right().eval(context);

    context.setQueueTarget(prevQ);
    if (!cl || !cr)
        return nullptr;

    if (value().type->hasFixedRange()) {
        optional<ConstantRange> range = getFixedRange(context, cl, cr);
        if (!range)
            return nullptr;

        if (value().type->isIntegral())
            lval.addBitSlice(*range);
        else
            lval.addArraySlice(*range, nullptr);
    }
    else {
        optional<ConstantRange> range = getDynamicRange(context, cl, cr, lval.load());
        if (!range)
            return nullptr;

        lval.addArraySlice(*range, type->getArrayElementType()->getDefaultValue());
    }

    return lval;
}

bool RangeSelectExpression::verifyConstantImpl(EvalContext& context) const {
    return value().verifyConstant(context) && left().verifyConstant(context) &&
           right().verifyConstant(context);
}

optional<ConstantRange> RangeSelectExpression::getFixedRange(EvalContext& context,
                                                             const ConstantValue& cl,
                                                             const ConstantValue& cr) const {
    ConstantRange result;
    const Type& valueType = *value().type;
    ConstantRange valueRange = valueType.getFixedRange();

    if (selectionKind == RangeSelectionKind::Simple) {
        result = type->getFixedRange();
    }
    else {
        optional<int32_t> l = cl.integer().as<int32_t>();
        if (!l) {
            context.addDiag(diag::ConstEvalArrayIndexInvalid, sourceRange) << cl << valueType;
            return std::nullopt;
        }

        optional<int32_t> r = cr.integer().as<int32_t>();
        ASSERT(r);
        result = ConstantRange::getIndexedRange(*l, *r, valueRange.isLittleEndian(),
                                                selectionKind == RangeSelectionKind::IndexedUp);
    }

    if (!valueRange.containsPoint(result.left) || !valueRange.containsPoint(result.right)) {
        auto& diag = context.addDiag(diag::ConstEvalPartSelectInvalid, sourceRange);
        diag << result.left << result.right;
        diag << valueType;
        return std::nullopt;
    }

    if (!valueType.isPackedArray()) {
        if (valueType.isUnpackedArray()) {
            // Unpacked arrays are stored reversed in memory, so reverse the range here.
            valueRange = valueRange.reverse();
        }
        result.left = valueRange.translateIndex(result.left);
        result.right = valueRange.translateIndex(result.right);
        return result;
    }

    // For packed arrays we're potentially selecting multi-bit elements.
    int32_t width = (int32_t)valueType.getArrayElementType()->getBitWidth();
    result.left = valueRange.translateIndex(result.left) * width + width - 1;
    result.right = valueRange.translateIndex(result.right) * width;

    return result;
}

optional<ConstantRange> RangeSelectExpression::getDynamicRange(EvalContext& context,
                                                               const ConstantValue& cl,
                                                               const ConstantValue& cr,
                                                               const ConstantValue& cv) const {
    const Type& valueType = *value().type;
    optional<int32_t> li = cl.integer().as<int32_t>();
    optional<int32_t> ri = cr.integer().as<int32_t>();
    if (!li) {
        context.addDiag(diag::ConstEvalArrayIndexInvalid, sourceRange) << cl << valueType;
        return std::nullopt;
    }
    if (!ri) {
        context.addDiag(diag::ConstEvalArrayIndexInvalid, sourceRange) << cr << valueType;
        return std::nullopt;
    }

    int32_t l = *li;
    int32_t r = *ri;
    ConstantRange result;

    if (selectionKind == RangeSelectionKind::Simple) {
        result = { l, r };
    }
    else {
        result = ConstantRange::getIndexedRange(l, r, false,
                                                selectionKind == RangeSelectionKind::IndexedUp);
    }

    // Out of bounds ranges are allowed, we just issue a warning.
    size_t size = cv.size();
    if (l < 0 || r < 0 || size_t(r) >= size) {
        auto& diag = context.addDiag(diag::ConstEvalDynamicArrayRange, sourceRange);
        diag << result.left << result.right;
        diag << valueType;
        diag << size;
    }

    return result;
}

void RangeSelectExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("selectionKind", toString(selectionKind));
    serializer.write("value", value());
    serializer.write("left", left());
    serializer.write("right", right());
}

static Expression* tryBindSpecialMethod(Compilation& compilation, const Expression& expr,
                                        const LookupResult::MemberSelector& selector,
                                        const InvocationExpressionSyntax* invocation,
                                        const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                        const BindContext& context) {
    auto sym = expr.getSymbolReference();
    if (!sym)
        return nullptr;

    // There is a built-in 'rand_mode' method that is present on every 'rand' and 'randc'
    // class property, and additionally on subelements of those properties.
    if (selector.name == "rand_mode"sv) {
        if (sym->getRandMode() == RandMode::None)
            return nullptr;

        return CallExpression::fromBuiltInMethod(compilation, SymbolKind::ClassProperty, expr,
                                                 selector, invocation, withClause, context);
    }

    return CallExpression::fromBuiltInMethod(compilation, sym->kind, expr, selector, invocation,
                                             withClause, context);
}

Expression& MemberAccessExpression::fromSelector(
    Compilation& compilation, Expression& expr, const LookupResult::MemberSelector& selector,
    const InvocationExpressionSyntax* invocation,
    const ArrayOrRandomizeMethodExpressionSyntax* withClause, const BindContext& context) {

    // If the selector name is invalid just give up early.
    if (selector.name.empty())
        return badExpr(compilation, &expr);

    // The source range of the entire member access starts from the value being selected.
    SourceRange range{ expr.sourceRange.start(), selector.nameRange.end() };

    // Special cases for built-in iterator methods that don't cleanly fit the general
    // mold of looking up members via the type of the expression.
    if (expr.kind == ExpressionKind::NamedValue) {
        auto symKind = expr.as<NamedValueExpression>().symbol.kind;
        if (symKind == SymbolKind::Iterator) {
            auto result = CallExpression::fromBuiltInMethod(compilation, symKind, expr, selector,
                                                            invocation, withClause, context);
            if (result)
                return *result;
        }
    }

    auto errorIfNotProcedural = [&] {
        if (context.flags.has(BindFlags::NonProcedural)) {
            context.addDiag(diag::DynamicNotProcedural, range);
            return true;
        }
        return false;
    };
    auto errorIfAssertion = [&] {
        if (context.flags.has(BindFlags::AssertionExpr)) {
            context.addDiag(diag::ClassMemberInAssertion, range);
            return true;
        }
        return false;
    };

    // This might look like a member access but actually be a built-in type method.
    const Type& type = expr.type->getCanonicalType();
    const Scope* scope = nullptr;
    switch (type.kind) {
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
        case SymbolKind::PackedUnionType:
        case SymbolKind::UnpackedUnionType:
        case SymbolKind::ClassType:
            scope = &type.as<Scope>();
            break;
        case SymbolKind::EnumType:
        case SymbolKind::StringType:
        case SymbolKind::FixedSizeUnpackedArrayType:
        case SymbolKind::DynamicArrayType:
        case SymbolKind::AssociativeArrayType:
        case SymbolKind::QueueType:
        case SymbolKind::EventType:
        case SymbolKind::SequenceType:
            return CallExpression::fromSystemMethod(compilation, expr, selector, invocation,
                                                    withClause, context);
        case SymbolKind::VirtualInterfaceType: {
            if (errorIfNotProcedural())
                return badExpr(compilation, &expr);

            auto& vi = type.as<VirtualInterfaceType>();
            if (vi.modport)
                scope = vi.modport;
            else
                scope = &vi.iface;
            break;
        }
        case SymbolKind::VoidType: {
            // This is possible via a clocking block accessed through a virtual interface,
            // so check for that case.
            if (expr.kind == ExpressionKind::MemberAccess) {
                auto sym = expr.getSymbolReference();
                if (sym && sym->kind == SymbolKind::ClockingBlock) {
                    scope = &sym->as<ClockingBlockSymbol>();
                    break;
                }
            }
            [[fallthrough]];
        }
        default: {
            if (auto result = tryBindSpecialMethod(compilation, expr, selector, invocation,
                                                   withClause, context)) {
                return *result;
            }

            auto& diag = context.addDiag(diag::InvalidMemberAccess, selector.dotLocation);
            diag << expr.sourceRange;
            diag << selector.nameRange;
            diag << *expr.type;
            return badExpr(compilation, &expr);
        }
    }

    const Symbol* member = scope->find(selector.name);
    if (!member) {
        if (auto result = tryBindSpecialMethod(compilation, expr, selector, invocation, withClause,
                                               context)) {
            return *result;
        }

        auto& diag = context.addDiag(diag::UnknownMember, selector.nameRange.start());
        diag << expr.sourceRange;
        diag << selector.name;
        diag << *expr.type;
        return badExpr(compilation, &expr);
    }

    switch (member->kind) {
        case SymbolKind::Field: {
            auto& field = member->as<FieldSymbol>();
            return *compilation.emplace<MemberAccessExpression>(field.getType(), expr, field,
                                                                field.offset, range);
        }
        case SymbolKind::ClassProperty: {
            Lookup::ensureVisible(*member, context, selector.nameRange);
            auto& prop = member->as<ClassPropertySymbol>();
            if (prop.lifetime == VariableLifetime::Automatic &&
                (errorIfNotProcedural() || errorIfAssertion())) {
                return badExpr(compilation, &expr);
            }

            return *compilation.emplace<MemberAccessExpression>(prop.getType(), expr, prop, 0u,
                                                                range);
        }
        case SymbolKind::Subroutine: {
            Lookup::ensureVisible(*member, context, selector.nameRange);
            auto& sub = member->as<SubroutineSymbol>();
            if (!sub.flags.has(MethodFlags::Static) &&
                (errorIfNotProcedural() || errorIfAssertion())) {
                return badExpr(compilation, &expr);
            }

            return CallExpression::fromLookup(compilation, &sub, &expr, invocation, withClause,
                                              range, context);
        }
        case SymbolKind::ConstraintBlock:
        case SymbolKind::ClockingBlock: {
            if (errorIfNotProcedural())
                return badExpr(compilation, &expr);
            return *compilation.emplace<MemberAccessExpression>(compilation.getVoidType(), expr,
                                                                *member, 0u, range);
        }
        default: {
            if (member->isValue()) {
                auto& value = member->as<ValueSymbol>();
                return *compilation.emplace<MemberAccessExpression>(value.getType(), expr, value,
                                                                    0u, range);
            }

            auto& diag = context.addDiag(diag::InvalidClassAccess, selector.dotLocation);
            diag << selector.nameRange;
            diag << expr.sourceRange;
            diag << selector.name;
            diag << *expr.type;
            return badExpr(compilation, &expr);
        }
    }
}

Expression& MemberAccessExpression::fromSyntax(
    Compilation& compilation, const MemberAccessExpressionSyntax& syntax,
    const InvocationExpressionSyntax* invocation,
    const ArrayOrRandomizeMethodExpressionSyntax* withClause, const BindContext& context) {

    auto name = syntax.name.valueText();
    Expression& lhs = selfDetermined(compilation, *syntax.left, context);
    if (lhs.bad() || name.empty())
        return badExpr(compilation, &lhs);

    LookupResult::MemberSelector selector;
    selector.name = name;
    selector.dotLocation = syntax.dot.location();
    selector.nameRange = syntax.name.range();

    auto& result = fromSelector(compilation, lhs, selector, invocation, withClause, context);
    if (result.kind != ExpressionKind::Call) {
        if (invocation) {
            auto& diag = context.addDiag(diag::ExpressionNotCallable, invocation->sourceRange());
            diag << selector.nameRange;
            return badExpr(compilation, &result);
        }

        if (withClause)
            context.addDiag(diag::UnexpectedWithClause, withClause->with.range());
    }

    return result;
}

// This iterator is used when translating values between different union members.
// It walks recursively down through unpacked struct members and allows retrieving
// corresponding constant values in member order, as long as they are equivalent
// with the next expected type.
class RecursiveStructMemberIterator {
public:
    RecursiveStructMemberIterator(const ConstantValue& startVal, const Type& startType) {
        curr.val = &startVal;
        curr.type = &startType;

        if (curr.type->isUnpackedStruct()) {
            auto range =
                curr.type->getCanonicalType().as<UnpackedStructType>().membersOfType<FieldSymbol>();
            curr.fieldIt = range.begin();
            curr.fieldEnd = range.end();
            prepNext();
        }
    }

    const ConstantValue* tryConsume(const Type& targetType) {
        if (!curr.type)
            return nullptr;

        if (!curr.type->isUnpackedStruct()) {
            if (!curr.type->isEquivalent(targetType))
                return nullptr;

            curr.type = nullptr;
            return curr.val;
        }

        if (!curr.fieldIt->getType().isEquivalent(targetType))
            return nullptr;

        auto result = &curr.val->at(curr.valIndex);
        curr.next();
        prepNext();
        return result;
    }

private:
    void prepNext() {
        if (curr.fieldIt == curr.fieldEnd) {
            if (stack.empty()) {
                curr.type = nullptr;
                return;
            }

            curr = stack.back();
            stack.pop();

            curr.next();
            prepNext();
        }
        else {
            auto& type = curr.fieldIt->getType();
            if (type.isUnpackedStruct()) {
                stack.emplace(curr);

                auto range =
                    type.getCanonicalType().as<UnpackedStructType>().membersOfType<FieldSymbol>();
                curr.type = &type;
                curr.val = &curr.val->at(curr.valIndex);
                curr.fieldIt = range.begin();
                curr.fieldEnd = range.end();
                curr.valIndex = 0;
                prepNext();
            }
        }
    }

    using FieldIt = Scope::specific_symbol_iterator<FieldSymbol>;

    struct State {
        const ConstantValue* val = nullptr;
        const Type* type = nullptr;
        size_t valIndex = 0;
        FieldIt fieldIt;
        FieldIt fieldEnd;

        void next() {
            fieldIt++;
            valIndex++;
        }
    };

    State curr;
    SmallVectorSized<State, 4> stack;
};

static bool translateUnionMembers(ConstantValue& result, const Type& targetType,
                                  RecursiveStructMemberIterator& rsmi) {
    // If the target type is still an unpacked struct then recurse deeper until we
    // reach a non-struct member that can be assigned a value.
    if (targetType.isUnpackedStruct()) {
        size_t i = 0;
        for (auto& member : targetType.as<UnpackedStructType>().membersOfType<FieldSymbol>()) {
            if (!translateUnionMembers(result.at(i++), member.getType().getCanonicalType(), rsmi)) {
                return false;
            }
        }
        return true;
    }

    auto val = rsmi.tryConsume(targetType);
    if (val) {
        result = *val;
        return true;
    }

    return false;
}

static bool checkPackedUnionTag(const Type& valueType, const SVInt& val, uint32_t expectedTag,
                                EvalContext& context, SourceRange sourceRange,
                                string_view memberName) {
    uint32_t tagBits = valueType.as<PackedUnionType>().tagBits;
    if (tagBits) {
        bitwidth_t bits = val.getBitWidth();
        auto tag = val.slice(int32_t(bits - 1), int32_t(bits - tagBits)).as<uint32_t>();
        if (tag.value() != expectedTag) {
            context.addDiag(diag::ConstEvalTaggedUnion, sourceRange) << memberName;
            return false;
        }
    }

    return true;
}

ConstantValue MemberAccessExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    if (!cv)
        return nullptr;

    auto& valueType = value().type->getCanonicalType();
    if (valueType.isUnpackedStruct()) {
        return cv.elements()[offset];
    }
    else if (valueType.isUnpackedUnion()) {
        auto& unionVal = cv.unionVal();
        if (unionVal->activeMember == offset)
            return unionVal->value;

        if (valueType.isTaggedUnion()) {
            // Tagged unions can only be accessed via their active member.
            context.addDiag(diag::ConstEvalTaggedUnion, sourceRange) << member.name;
            return nullptr;
        }
        else {
            // This member isn't active, so in general it's not safe (or even
            // possible) to access it. An exception is made for the common initial
            // sequence of equivalent types, so check for that here and if found
            // translate the values across.
            ConstantValue result = type->getDefaultValue();
            if (unionVal->activeMember) {
                // Get the type of the member that is currently active.
                auto& currType = valueType.as<UnpackedUnionType>()
                                     .memberAt<FieldSymbol>(*unionVal->activeMember)
                                     .getType()
                                     .getCanonicalType();

                RecursiveStructMemberIterator rsmi(unionVal->value, currType);
                translateUnionMembers(result, type->getCanonicalType(), rsmi);
            }
            return result;
        }
    }
    else if (valueType.isPackedUnion()) {
        auto& cvi = cv.integer();
        if (!checkPackedUnionTag(valueType, cvi, offset, context, sourceRange, member.name)) {
            return nullptr;
        }

        return cvi.slice(int32_t(type->getBitWidth() - 1), 0);
    }
    else {
        int32_t io = (int32_t)offset;
        int32_t width = (int32_t)type->getBitWidth();
        return cv.integer().slice(width + io - 1, io);
    }
}

LValue MemberAccessExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    if (!lval)
        return nullptr;

    int32_t io = (int32_t)offset;
    auto& valueType = value().type->getCanonicalType();
    if (valueType.isUnpackedStruct()) {
        lval.addIndex(io, nullptr);
    }
    else if (valueType.isUnpackedUnion()) {
        if (valueType.isTaggedUnion()) {
            auto target = lval.resolve();
            ASSERT(target);

            if (target->unionVal()->activeMember != offset) {
                context.addDiag(diag::ConstEvalTaggedUnion, sourceRange) << member.name;
                return nullptr;
            }
        }
        lval.addIndex(io, type->getDefaultValue());
    }
    else if (valueType.isPackedUnion()) {
        auto cv = lval.load();
        if (!checkPackedUnionTag(valueType, cv.integer(), offset, context, sourceRange,
                                 member.name)) {
            return nullptr;
        }

        int32_t width = (int32_t)type->getBitWidth();
        lval.addBitSlice({ width - 1, 0 });
    }
    else {
        int32_t width = (int32_t)type->getBitWidth();
        lval.addBitSlice({ width + io - 1, io });
    }

    return lval;
}

bool MemberAccessExpression::verifyConstantImpl(EvalContext& context) const {
    return value().verifyConstant(context);
}

bool MemberAccessExpression::verifyAssignableImpl(const BindContext& context,
                                                  SourceLocation location, bool isNonBlocking,
                                                  bool inConcat) const {
    // If this is a selection of a class member, assignability depends only on the selected
    // member and not on the class handle itself. Otherwise, the opposite is true.
    auto& valueType = *value().type;
    if (!valueType.isClass() && !valueType.isVirtualInterface() && !valueType.isVoid())
        return value().verifyAssignable(context, location, isNonBlocking, inConcat);

    if (VariableSymbol::isKind(member.kind)) {
        return context.requireAssignable(member.as<VariableSymbol>(), isNonBlocking, location,
                                         sourceRange);
    }

    // TODO: modport assignability checks
    if (member.kind == SymbolKind::ModportPort)
        return true;

    if (!location)
        location = sourceRange.start();

    auto& diag = context.addDiag(diag::ExpressionNotAssignable, location);
    diag.addNote(diag::NoteDeclarationHere, member.location);
    diag << sourceRange;
    return false;
}

void MemberAccessExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.writeLink("member", member);
    serializer.write("value", value());
}

} // namespace slang
