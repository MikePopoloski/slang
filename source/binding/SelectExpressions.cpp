//------------------------------------------------------------------------------
// SelectExpressions.cpp
// Definitions for selection expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SelectExpressions.h"

#include "slang/binding/LiteralExpressions.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/ClassSymbols.h"
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
        selector = &selfDetermined(compilation, syntax, context);
        if (!selector->bad() && !selector->type->isIntegral()) {
            context.addDiag(diag::ExprMustBeIntegral, selector->sourceRange);
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
    ConstantValue cs = selector().eval(context);
    if (!cv || !cs)
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
    ConstantValue cs = selector().eval(context);
    if (!lval || !cs)
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

    const Expression& left = leftConst ? bind(*syntax.left, context, BindFlags::Constant)
                                       : selfDetermined(compilation, *syntax.left, context);
    const Expression& right = rightConst ? bind(*syntax.right, context, BindFlags::Constant)
                                         : selfDetermined(compilation, *syntax.right, context);

    auto result = compilation.emplace<RangeSelectExpression>(
        selectionKind, compilation.getErrorType(), value, left, right, fullRange);

    if (value.bad() || left.bad() || right.bad())
        return badExpr(compilation, result);

    if (!left.type->isIntegral()) {
        context.addDiag(diag::ExprMustBeIntegral, left.sourceRange);
        return badExpr(compilation, result);
    }
    if (!right.type->isIntegral()) {
        context.addDiag(diag::ExprMustBeIntegral, right.sourceRange);
        return badExpr(compilation, result);
    }

    const Type& valueType = *value.type;
    const Type& elementType = getIndexedType(compilation, context, valueType, syntax.sourceRange(),
                                             value.sourceRange, true);
    if (elementType.isError())
        return badExpr(compilation, result);

    // Selects of vectored nets are disallowed.
    checkForVectoredSelect(value, fullRange, context);

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
                    getIndexedRange(selectionKind, *index, *rv, valueRange.isLittleEndian());

                if (!validateRange(selectionRange))
                    return badExpr(compilation, result);
            }
            else {
                // Otherwise, the resulting range will start with the fixed lower bound of the type.
                int32_t l = selectionKind == RangeSelectionKind::IndexedUp ? valueRange.lower()
                                                                           : valueRange.upper();
                selectionRange =
                    getIndexedRange(selectionKind, l, *rv, valueRange.isLittleEndian());
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
    ConstantValue cl = left().eval(context);
    ConstantValue cr = right().eval(context);
    if (!cv || !cl || !cr)
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
    ConstantValue cl = left().eval(context);
    ConstantValue cr = right().eval(context);
    if (!lval || !cl || !cr)
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
        result = getIndexedRange(selectionKind, *l, *r, valueRange.isLittleEndian());
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
        result = getIndexedRange(selectionKind, l, r, false);
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

ConstantRange RangeSelectExpression::getIndexedRange(RangeSelectionKind kind, int32_t l, int32_t r,
                                                     bool littleEndian) {
    ConstantRange result;
    int32_t count = r - 1;
    if (kind == RangeSelectionKind::IndexedUp) {
        auto upper = checkedAddS32(l, count);
        if (!upper)
            upper = INT32_MAX;

        result.left = *upper;
        result.right = l;
    }
    else {
        auto lower = checkedSubS32(l, count);
        if (!lower)
            lower = INT32_MIN;

        result.left = l;
        result.right = *lower;
    }

    if (!littleEndian)
        return result.reverse();

    return result;
}

void RangeSelectExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("selectionKind", toString(selectionKind));
    serializer.write("value", value());
    serializer.write("left", left());
    serializer.write("right", right());
}

Expression& MemberAccessExpression::fromSelector(
    Compilation& compilation, Expression& expr, const LookupResult::MemberSelector& selector,
    const InvocationExpressionSyntax* invocation,
    const ArrayOrRandomizeMethodExpressionSyntax* withClause, const BindContext& context) {

    // If the selector name is invalid just give up early.
    if (selector.name.empty())
        return badExpr(compilation, &expr);

    // This might look like a member access but actually be a built-in type method.
    const Type& type = expr.type->getCanonicalType();
    switch (type.kind) {
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
        case SymbolKind::PackedUnionType:
        case SymbolKind::UnpackedUnionType:
        case SymbolKind::ClassType:
            break;
        case SymbolKind::EnumType:
        case SymbolKind::StringType:
        case SymbolKind::FixedSizeUnpackedArrayType:
        case SymbolKind::DynamicArrayType:
        case SymbolKind::AssociativeArrayType:
        case SymbolKind::QueueType:
        case SymbolKind::EventType:
            return CallExpression::fromSystemMethod(compilation, expr, selector, invocation,
                                                    withClause, context);
        default: {
            auto& diag = context.addDiag(diag::InvalidMemberAccess, selector.dotLocation);
            diag << expr.sourceRange;
            diag << selector.nameRange;
            diag << *expr.type;
            return badExpr(compilation, &expr);
        }
    }

    const Symbol* member = expr.type->getCanonicalType().as<Scope>().find(selector.name);
    if (!member) {
        auto& diag = context.addDiag(diag::UnknownMember, selector.nameRange.start());
        diag << expr.sourceRange;
        diag << selector.name;
        diag << *expr.type;
        return badExpr(compilation, &expr);
    }

    // The source range of the entire member access starts from the value being selected.
    SourceRange range{ expr.sourceRange.start(), selector.nameRange.end() };

    switch (member->kind) {
        case SymbolKind::Field: {
            auto& field = member->as<FieldSymbol>();
            return *compilation.emplace<MemberAccessExpression>(field.getType(), expr, field,
                                                                field.offset, range);
        }
        case SymbolKind::ClassProperty: {
            Lookup::ensureVisible(*member, context, selector.nameRange);
            auto& prop = member->as<ClassPropertySymbol>();
            return *compilation.emplace<MemberAccessExpression>(prop.getType(), expr, prop, 0u,
                                                                range);
        }
        case SymbolKind::Subroutine:
            Lookup::ensureVisible(*member, context, selector.nameRange);
            return CallExpression::fromLookup(compilation, &member->as<SubroutineSymbol>(), &expr,
                                              invocation, withClause, range, context);
        case SymbolKind::EnumValue: {
            auto& value = member->as<EnumValueSymbol>();
            return *compilation.emplace<MemberAccessExpression>(value.getType(), expr, value, 0u,
                                                                range);
        }
        case SymbolKind::Parameter: {
            auto& value = member->as<ParameterSymbol>();
            return *compilation.emplace<MemberAccessExpression>(value.getType(), expr, value, 0u,
                                                                range);
        }
        default:
            auto& diag = context.addDiag(diag::InvalidClassAccess, selector.dotLocation);
            diag << selector.nameRange;
            diag << expr.sourceRange;
            diag << selector.name;
            diag << *expr.type;
            return badExpr(compilation, &expr);
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

ConstantValue MemberAccessExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    if (!cv)
        return nullptr;

    // TODO: handle unpacked unions
    if (value().type->isUnpackedStruct())
        return cv.elements()[offset];

    int32_t io = (int32_t)offset;
    int32_t width = (int32_t)type->getBitWidth();
    return cv.integer().slice(width + io - 1, io);
}

LValue MemberAccessExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    if (!lval)
        return nullptr;

    // TODO: handle unpacked unions
    int32_t io = (int32_t)offset;
    if (value().type->isUnpackedStruct()) {
        lval.addIndex(io, nullptr);
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

bool MemberAccessExpression::verifyAssignableImpl(const BindContext& context, bool isNonBlocking,
                                                  SourceLocation location) const {
    // If this is a selection of a class member, assignability depends only on the selected
    // member and not on the class handle itself. Otherwise, the opposite is true.
    if (!value().type->isClass())
        return value().verifyAssignable(context, isNonBlocking, location);

    if (VariableSymbol::isKind(member.kind)) {
        return context.requireAssignable(member.as<VariableSymbol>(), isNonBlocking, location,
                                         sourceRange);
    }

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
