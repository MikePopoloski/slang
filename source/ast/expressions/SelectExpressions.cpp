//------------------------------------------------------------------------------
// SelectExpressions.cpp
// Definitions for selection expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/expressions/SelectExpressions.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/ast/expressions/LiteralExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/CoverSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/NetType.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;

static const Type& getIndexedType(Compilation& compilation, const ASTContext& context,
                                  const Type& valueType, SourceRange exprRange,
                                  SourceRange valueRange, bool isRangeSelect) {
    const Type& ct = valueType.getCanonicalType();
    if (ct.isArray()) {
        auto& elemType = *ct.getArrayElementType();
        if (valueType.kind == SymbolKind::PackedArrayType && valueType.isSigned())
            return elemType.makeUnsigned(compilation);

        return elemType;
    }
    else if (ct.kind == SymbolKind::StringType && !isRangeSelect) {
        return compilation.getByteType();
    }
    else if (!ct.isIntegral()) {
        if (!ct.isError()) {
            auto code = isRangeSelect ? diag::BadSliceType : diag::BadIndexExpression;
            auto& diag = context.addDiag(code, exprRange);
            diag << valueRange;
            diag << valueType;
        }
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

static void checkForVectoredSelect(const Expression& value, SourceRange range,
                                   const ASTContext& context) {
    if (value.kind != ExpressionKind::NamedValue && value.kind != ExpressionKind::HierarchicalValue)
        return;

    const Symbol& sym = value.as<ValueExpressionBase>().symbol;
    if (sym.kind == SymbolKind::Net && sym.as<NetSymbol>().expansionHint == NetSymbol::Vectored) {
        auto& diag = context.addDiag(diag::SelectOfVectoredNet, range);
        diag.addNote(diag::NoteDeclarationHere, sym.location);
    }
}

template<typename T>
bool requireLValueHelper(const T& expr, const ASTContext& context, SourceLocation location,
                         bitmask<AssignFlags> flags, const Expression* longestStaticPrefix) {
    auto& val = expr.value();
    if (val.kind == ExpressionKind::Concatenation || val.kind == ExpressionKind::Streaming) {
        // Selects of concatenations are not allowed to be lvalues.
        if (!location)
            location = expr.sourceRange.start();

        auto& diag = context.addDiag(diag::ExpressionNotAssignable, location);
        diag << expr.sourceRange;
        return false;
    }

    if (ValueExpressionBase::isKind(val.kind)) {
        auto& sym = val.template as<ValueExpressionBase>().symbol;
        if (sym.kind == SymbolKind::Net) {
            if (sym.template as<NetSymbol>().netType.netKind == NetType::UserDefined) {
                context.addDiag(diag::UserDefPartialDriver, expr.sourceRange) << sym.name;
                return false;
            }
        }

        if (flags.has(AssignFlags::NonBlocking) && sym.getType().isDynamicallySizedArray()) {
            if (!location)
                location = expr.sourceRange.start();

            context.addDiag(diag::NonblockingDynamicAssign, location) << expr.sourceRange;
            return false;
        }
    }

    if (context.flags.has(ASTFlags::NonProcedural)) {
        if constexpr (std::is_same_v<T, RangeSelectExpression>) {
            if (!context.eval(expr.left()) || !context.eval(expr.right()))
                return false;
        }
        else {
            if (!context.eval(expr.selector()))
                return false;
        }

        if (!longestStaticPrefix)
            longestStaticPrefix = &expr;
    }
    else {
        EvalContext evalCtx(context, EvalFlags::CacheResults);
        if (expr.isConstantSelect(evalCtx)) {
            if (!longestStaticPrefix)
                longestStaticPrefix = &expr;
        }
        else {
            longestStaticPrefix = nullptr;
        }
    }

    return val.requireLValue(context, location, flags, longestStaticPrefix);
}

Expression& ElementSelectExpression::fromSyntax(Compilation& compilation, Expression& value,
                                                const ExpressionSyntax& syntax,
                                                SourceRange fullRange, const ASTContext& context) {
    // Selects of vectored nets are disallowed.
    checkForVectoredSelect(value, fullRange, context);

    const Type& valueType = *value.type;
    const Type& resultType = getIndexedType(compilation, context, valueType, syntax.sourceRange(),
                                            value.sourceRange, false);

    // The selector expression is never an lvalue, even if we are otherwise
    // in an lvalue context.
    ASTContext selectorCtx = context;
    selectorCtx.flags &= ~ASTFlags::LValue;

    // If this is an associative array with a specific index target, we need to bind
    // as an rvalue to get the right conversion applied.
    const Expression* selector = nullptr;
    if (valueType.isAssociativeArray()) {
        auto indexType = valueType.getAssociativeIndexType();
        if (indexType)
            selector = &bindRValue(*indexType, syntax, {}, selectorCtx);
    }

    if (!selector) {
        bitmask<ASTFlags> flags;
        if (valueType.isQueue() || valueType.isError())
            flags = ASTFlags::AllowUnboundedLiteral | ASTFlags::AllowUnboundedLiteralArithmetic;

        selector = &selfDetermined(compilation, syntax, selectorCtx, flags);
        if (!selector->type->isUnbounded() && !value.bad() &&
            !selectorCtx.requireIntegral(*selector)) {
            return badExpr(compilation, nullptr);
        }
    }

    auto result = compilation.emplace<ElementSelectExpression>(resultType, value, *selector,
                                                               fullRange);
    if (value.bad() || selector->bad() || result->bad())
        return badExpr(compilation, result);

    // If the selector is constant, and the underlying type has a fixed range,
    // we can do checking at compile time that it's within bounds.
    // Only do that if we're not in an unevaluated conditional branch.
    if (valueType.hasFixedRange()) {
        ConstantValue selVal;
        if (!context.inUnevaluatedBranch() && (selVal = context.tryEval(*selector))) {
            std::optional<int32_t> index = selVal.integer().as<int32_t>();
            if (!index || !valueType.getFixedRange().containsPoint(*index)) {
                auto& diag = context.addDiag(diag::IndexOOB, selector->sourceRange);
                diag << selVal;
                diag << *value.type;

                // Don't return an error -- this diagnostic can be suppressed
                // and the LRM defines what an out of bounds access resolves to.
                result->warnedAboutIndex = true;
            }
        }
    }
    else if (context.flags.has(ASTFlags::NonProcedural)) {
        context.addDiag(diag::DynamicNotProcedural, fullRange);
        return badExpr(compilation, result);
    }

    return *result;
}

Expression& ElementSelectExpression::fromConstant(Compilation& compilation, Expression& value,
                                                  int32_t index, const ASTContext& context) {
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

bool ElementSelectExpression::isConstantSelect(EvalContext& context) const {
    return value().type->hasFixedRange() && !selector().eval(context).bad();
}

ConstantValue ElementSelectExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    if (!cv)
        return nullptr;

    bool softFail = false;
    ConstantValue associativeIndex;
    auto range = evalIndex(context, cv, associativeIndex, softFail);
    if (!range && associativeIndex.bad()) {
        if (softFail)
            return type->getDefaultValue();
        else
            return nullptr;
    }

    // Handling for packed and unpacked arrays, all integer types.
    const Type& valType = *value().type;
    if (valType.hasFixedRange()) {
        // For fixed types, we know we will always be in range, so just do the selection.
        if (valType.isUnpackedArray())
            return cv.elements()[size_t(range->left)];
        else
            return cv.integer().slice(range->left, range->right);
    }

    // Handling for associative arrays.
    if (valType.isAssociativeArray()) {
        auto& map = *cv.map();
        if (auto it = map.find(associativeIndex); it != map.end())
            return it->second;

        // If there is a user specified default, return that without warning.
        if (map.defaultValue)
            return map.defaultValue;

        // Otherwise issue a warning and use the default default.
        context.addDiag(diag::ConstEvalAssociativeElementNotFound, selector().sourceRange)
            << value().sourceRange << associativeIndex;
        return type->getDefaultValue();
    }

    // Handling for strings, dynamic arrays, and queues.
    SLANG_ASSERT(range->left == range->right);
    if (valType.isString())
        return cv.getSlice(range->left, range->right, nullptr);

    return std::move(cv).at(size_t(range->left));
}

LValue ElementSelectExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    if (!lval)
        return nullptr;

    ConstantValue loadedVal;
    if (!value().type->hasFixedRange())
        loadedVal = lval.load();

    bool softFail = false;
    ConstantValue associativeIndex;
    auto range = evalIndex(context, loadedVal, associativeIndex, softFail);
    if (!range && associativeIndex.bad()) {
        if (!softFail)
            return nullptr;

        // Add an out of bounds entry so that reads will return the default
        // and writes will be ignored.
        lval.addIndexOutOfBounds(type->getDefaultValue());
        return lval;
    }

    // Handling for packed and unpacked arrays, all integer types.
    const Type& valType = *value().type;
    if (valType.hasFixedRange()) {
        // For fixed types, we know we will always be in range, so just do the selection.
        if (valType.isUnpackedArray())
            lval.addIndex(range->left, type->getDefaultValue());
        else
            lval.addBitSlice(*range);
        return lval;
    }

    // Handling for associative arrays.
    if (valType.isAssociativeArray()) {
        lval.addArrayLookup(std::move(associativeIndex), type->getDefaultValue());
        return lval;
    }

    // Handling for strings, dynamic arrays, and queues.
    SLANG_ASSERT(range->left == range->right);
    lval.addIndex(range->left, type->getDefaultValue());

    return lval;
}

std::optional<ConstantRange> ElementSelectExpression::evalIndex(EvalContext& context,
                                                                const ConstantValue& val,
                                                                ConstantValue& associativeIndex,
                                                                bool& softFail) const {
    auto prevQ = context.getQueueTarget();
    if (val.isQueue())
        context.setQueueTarget(&val);

    ConstantValue cs = selector().eval(context);

    context.setQueueTarget(prevQ);
    if (!cs)
        return std::nullopt;

    const Type& valType = *value().type;
    if (valType.isAssociativeArray()) {
        if (cs.hasUnknown())
            context.addDiag(diag::ConstEvalAssociativeIndexInvalid, selector().sourceRange) << cs;
        else
            associativeIndex = std::move(cs);
        softFail = true;
        return std::nullopt;
    }

    std::optional<int32_t> index = cs.integer().as<int32_t>();
    if (!index) {
        if (!warnedAboutIndex)
            context.addDiag(diag::IndexOOB, sourceRange) << cs << valType;
        softFail = true;
        return std::nullopt;
    }

    if (valType.hasFixedRange()) {
        ConstantRange range = valType.getFixedRange();
        if (!range.containsPoint(*index)) {
            if (!warnedAboutIndex)
                context.addDiag(diag::IndexOOB, sourceRange) << cs << valType;
            softFail = true;
            return std::nullopt;
        }

        if (valType.isUnpackedArray()) {
            // Unpacked arrays are stored reversed in memory, so reverse the range here.
            range = range.reverse();
            int32_t i = range.translateIndex(*index);
            return ConstantRange{i, i};
        }

        // For packed arrays, we're selecting bit ranges, not necessarily single bits,
        // so multiply out by the width of each element.
        int32_t width = (int32_t)type->getBitWidth();
        int32_t i = range.translateIndex(*index) * width;
        return ConstantRange{i + width - 1, i};
    }

    if (val) {
        size_t maxIndex = val.size();
        if (val.isQueue())
            maxIndex++;

        if (*index < 0 || size_t(*index) >= maxIndex) {
            context.addDiag(diag::ConstEvalDynamicArrayIndex, sourceRange)
                << cs << valType << maxIndex;
            softFail = true;
            return std::nullopt;
        }
    }
    else if (*index < 0) {
        context.addDiag(diag::IndexOOB, sourceRange) << cs << valType;
        softFail = true;
        return std::nullopt;
    }

    return ConstantRange{*index, *index};
}

bool ElementSelectExpression::requireLValueImpl(const ASTContext& context, SourceLocation location,
                                                bitmask<AssignFlags> flags,
                                                const Expression* longestStaticPrefix) const {
    return requireLValueHelper(*this, context, location, flags, longestStaticPrefix);
}

void ElementSelectExpression::getLongestStaticPrefixesImpl(
    SmallVector<std::pair<const ValueSymbol*, const Expression*>>& results,
    EvalContext& evalContext, const Expression* longestStaticPrefix) const {

    if (isConstantSelect(evalContext)) {
        if (!longestStaticPrefix)
            longestStaticPrefix = this;
    }
    else {
        longestStaticPrefix = nullptr;
    }

    value().getLongestStaticPrefixes(results, evalContext, longestStaticPrefix);
}

void ElementSelectExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("value", value());
    serializer.write("selector", selector());
}

template<typename TContext>
static bool checkRangeOverflow(ConstantRange range, TContext& context, SourceRange sourceRange) {
    if (range.fullWidth() > INT32_MAX) {
        context.addDiag(diag::RangeWidthOverflow, sourceRange);
        return true;
    }
    return false;
}

Expression& RangeSelectExpression::fromSyntax(Compilation& compilation, Expression& value,
                                              const RangeSelectSyntax& syntax,
                                              SourceRange fullRange, const ASTContext& context) {
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
            SLANG_UNREACHABLE;
    }

    if (!value.bad() && value.type->isAssociativeArray()) {
        context.addDiag(diag::RangeSelectAssociative, fullRange);
        return badExpr(compilation, nullptr);
    }

    // Selection expressions don't need to be const if we're selecting from a queue.
    bitmask<ASTFlags> extraFlags;
    bool isQueue = value.type->isQueue();
    if (isQueue || value.bad())
        extraFlags = ASTFlags::AllowUnboundedLiteral | ASTFlags::AllowUnboundedLiteralArithmetic;

    // The selector expressions are never lvalues, even if we are otherwise
    // in an lvalue context.
    ASTContext selectorCtx = context;
    selectorCtx.flags &= ~ASTFlags::LValue;

    auto& left = bind(*syntax.left, selectorCtx, extraFlags);
    auto& right = bind(*syntax.right, selectorCtx, extraFlags);

    auto result = compilation.emplace<RangeSelectExpression>(selectionKind,
                                                             compilation.getErrorType(), value,
                                                             left, right, fullRange);

    if (value.bad() || left.bad() || right.bad())
        return badExpr(compilation, result);

    if (!left.type->isUnbounded() && !context.requireIntegral(left))
        return badExpr(compilation, result);

    if (!right.type->isUnbounded() && !context.requireIntegral(right))
        return badExpr(compilation, result);

    const Type& valueType = *value.type;
    const Type& elementType = getIndexedType(compilation, context, valueType, syntax.sourceRange(),
                                             value.sourceRange, true);
    if (elementType.isError())
        return badExpr(compilation, result);

    // Selects of vectored nets are disallowed.
    checkForVectoredSelect(value, fullRange, context);

    if (!valueType.hasFixedRange() && context.flags.has(ASTFlags::NonProcedural)) {
        context.addDiag(diag::DynamicNotProcedural, fullRange);
        return badExpr(compilation, result);
    }

    // If this is selecting from a queue, the result is always a queue.
    if (isQueue) {
        result->type = compilation.emplace<QueueType>(elementType, 0u);
        return *result;
    }

    // If this is a streaming concatenation's "with" range, we also don't
    // require a constant width, but we'll try to validate it if we see
    // that the bounds are constant anyway.
    if (context.flags.has(ASTFlags::StreamingWithRange)) {
        if (context.inUnevaluatedBranch() || !context.tryEval(right) ||
            (selectionKind == RangeSelectionKind::Simple && !context.tryEval(left))) {
            result->type = compilation.emplace<QueueType>(elementType, 0u);
            return *result;
        }
    }

    std::optional<int32_t> rv = context.evalInteger(right);
    if (!rv)
        return badExpr(compilation, result);

    // If the array type has a fixed range, validate that the range we're selecting is allowed.
    SourceRange errorRange{left.sourceRange.start(), right.sourceRange.end()};
    if (valueType.hasFixedRange()) {
        ConstantRange selectionRange;
        ConstantRange valueRange = valueType.getFixedRange();

        // Helper function for validating the bounds of the selection.
        auto validateRange = [&](ConstantRange range) {
            if (!valueRange.containsPoint(range.left) || !valueRange.containsPoint(range.right)) {
                auto& diag = context.addDiag(diag::RangeOOB, errorRange);
                diag << range.left << range.right;
                diag << valueType;

                result->warnedAboutRange = true;
            }
        };

        if (selectionKind == RangeSelectionKind::Simple) {
            std::optional<int32_t> lv = context.evalInteger(left);
            if (!lv)
                return badExpr(compilation, result);

            selectionRange = {*lv, *rv};
            if (checkRangeOverflow(selectionRange, context, errorRange))
                return badExpr(compilation, result);

            if (selectionRange.isLittleEndian() != valueRange.isLittleEndian() &&
                selectionRange.width() > 1) {
                auto& diag = context.addDiag(diag::SelectEndianMismatch, errorRange);
                diag << valueType;
                return badExpr(compilation, result);
            }

            if (!context.inUnevaluatedBranch())
                validateRange(selectionRange);
        }
        else {
            if (!context.requireGtZero(rv, right.sourceRange))
                return badExpr(compilation, result);

            // If the lhs is a known constant, we can check that now too.
            ConstantValue leftVal;
            if (!context.inUnevaluatedBranch() && (leftVal = context.tryEval(left))) {
                std::optional<int32_t> index = leftVal.integer().as<int32_t>();
                if (!index) {
                    auto& diag = context.addDiag(diag::IndexValueInvalid, left.sourceRange);
                    diag << leftVal;
                    diag << valueType;
                    return badExpr(compilation, result);
                }

                auto range =
                    ConstantRange::getIndexedRange(*index, *rv, valueRange.isLittleEndian(),
                                                   selectionKind == RangeSelectionKind::IndexedUp);
                if (!range) {
                    context.addDiag(diag::RangeWidthOverflow, errorRange);
                    return badExpr(compilation, result);
                }

                selectionRange = *range;
                validateRange(selectionRange);
            }
            else {
                // Otherwise, the resulting range will start with the fixed lower bound of the type.
                int32_t l = selectionKind == RangeSelectionKind::IndexedUp ? valueRange.lower()
                                                                           : valueRange.upper();
                auto range = ConstantRange::getIndexedRange(l, *rv, valueRange.isLittleEndian(),
                                                            selectionKind ==
                                                                RangeSelectionKind::IndexedUp);
                if (!range) {
                    context.addDiag(diag::RangeWidthOverflow, errorRange);
                    return badExpr(compilation, result);
                }

                selectionRange = *range;

                if (bitwidth_t(*rv) > valueRange.width()) {
                    auto& diag = context.addDiag(diag::RangeWidthOOB, right.sourceRange);
                    diag << *rv;
                    diag << valueType;
                }
            }
        }

        // At this point, all expressions are good, ranges have been validated and
        // we know the final width of the selection, so pick the result type and we're done.
        if (valueType.isUnpackedArray()) {
            result->type = &FixedSizeUnpackedArrayType::fromDim(*context.scope, elementType,
                                                                selectionRange, errorRange);
        }
        else {
            result->type = &PackedArrayType::fromDim(*context.scope, elementType, selectionRange,
                                                     errorRange);
        }
    }
    else {
        // Otherwise, this is a dynamic array so we can't validate much. We should check that
        // the selection endianness is correct for simple ranges -- dynamic arrays only
        // permit big endian [0..N] ordering.
        ConstantRange selectionRange;
        if (selectionKind == RangeSelectionKind::Simple) {
            std::optional<int32_t> lv = context.evalInteger(left);
            if (!lv)
                return badExpr(compilation, result);

            selectionRange = {*lv, *rv};
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

        result->type = &FixedSizeUnpackedArrayType::fromDim(*context.scope, elementType,
                                                            selectionRange, errorRange);
    }

    return *result;
}

Expression& RangeSelectExpression::fromConstant(Compilation& compilation, Expression& value,
                                                ConstantRange range, const ASTContext& context) {
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
    const Type& elementType = getIndexedType(compilation, context, valueType, value.sourceRange,
                                             value.sourceRange, true);

    if (elementType.isError())
        return badExpr(compilation, result);

    // This method is only called on expressions with a fixed range type.
    SLANG_ASSERT(range.isLittleEndian() == valueType.getFixedRange().isLittleEndian());
    SLANG_ASSERT(valueType.hasFixedRange());

    if (valueType.isUnpackedArray()) {
        result->type = &FixedSizeUnpackedArrayType::fromDim(*context.scope, elementType, range,
                                                            result->sourceRange);
    }
    else {
        result->type = &PackedArrayType::fromDim(*context.scope, elementType, range,
                                                 result->sourceRange);
    }

    return *result;
}

bool RangeSelectExpression::isConstantSelect(EvalContext& context) const {
    return value().type->hasFixedRange() && left().eval(context) && right().eval(context);
}

ConstantValue RangeSelectExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    if (!cv)
        return nullptr;

    auto range = evalRange(context, cv, /* enforceBounds */ false);
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

LValue RangeSelectExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    if (!lval)
        return nullptr;

    ConstantValue loadedVal;
    if (!value().type->hasFixedRange())
        loadedVal = lval.load();

    auto range = evalRange(context, loadedVal, /* enforceBounds */ false);
    if (!range)
        return nullptr;

    if (value().type->isIntegral())
        lval.addBitSlice(*range);
    else
        lval.addArraySlice(*range, type->getArrayElementType()->getDefaultValue());

    return lval;
}

std::optional<ConstantRange> RangeSelectExpression::evalRange(EvalContext& context,
                                                              const ConstantValue& val,
                                                              bool enforceBounds) const {
    auto prevQ = context.getQueueTarget();
    if (val.isQueue())
        context.setQueueTarget(&val);

    ConstantValue cl = left().eval(context);
    ConstantValue cr = right().eval(context);

    context.setQueueTarget(prevQ);
    if (!cl || !cr)
        return std::nullopt;

    const Type& valueType = *value().type;
    std::optional<int32_t> li = cl.integer().as<int32_t>();
    std::optional<int32_t> ri = cr.integer().as<int32_t>();
    if (!li) {
        context.addDiag(diag::IndexValueInvalid, left().sourceRange) << cl << valueType;
        return std::nullopt;
    }
    if (!ri) {
        context.addDiag(diag::IndexValueInvalid, right().sourceRange) << cr << valueType;
        return std::nullopt;
    }

    ConstantRange result;
    if (selectionKind == RangeSelectionKind::Simple) {
        result = {*li, *ri};
        if (checkRangeOverflow(result, context, sourceRange))
            return std::nullopt;
    }
    else {
        bool isLittleEndian = false;
        if (valueType.hasFixedRange())
            isLittleEndian = valueType.getFixedRange().isLittleEndian();

        auto range = ConstantRange::getIndexedRange(*li, *ri, isLittleEndian,
                                                    selectionKind == RangeSelectionKind::IndexedUp);
        if (!range) {
            context.addDiag(diag::RangeWidthOverflow, sourceRange);
            return std::nullopt;
        }

        result = *range;
    }

    if (valueType.hasFixedRange()) {
        ConstantRange valueRange = valueType.getFixedRange();
        if (!warnedAboutRange &&
            (!valueRange.containsPoint(result.left) || !valueRange.containsPoint(result.right))) {
            auto& diag = context.addDiag(diag::RangeOOB, sourceRange);
            diag << result.left << result.right;
            diag << valueType;
        }

        if (enforceBounds) {
            result.left = std::min(std::max(result.left, valueRange.lower()), valueRange.upper());
            result.right = std::min(std::max(result.right, valueRange.lower()), valueRange.upper());
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

    // Out of bounds ranges are allowed, we just issue a warning.
    if (!val.bad()) {
        size_t size = val.size();
        if (result.left < 0 || result.right < 0 || size_t(result.left) >= size ||
            size_t(result.right) >= size) {

            auto& diag = context.addDiag(diag::ConstEvalDynamicArrayRange, sourceRange);
            diag << result.left << result.right;
            diag << valueType;
            diag << size;
        }

        if (enforceBounds) {
            result.left = std::min(std::max(result.left, 0), int32_t(size));
            result.right = std::min(std::max(result.right, 0), int32_t(size));
        }
    }
    else if (result.left < 0 || result.right < 0) {
        auto& diag = context.addDiag(diag::RangeOOB, sourceRange);
        diag << result.left << result.right;
        diag << valueType;

        if (enforceBounds) {
            result.left = std::max(result.left, 0);
            result.right = std::max(result.right, 0);
        }
    }

    return result;
}

bool RangeSelectExpression::requireLValueImpl(const ASTContext& context, SourceLocation location,
                                              bitmask<AssignFlags> flags,
                                              const Expression* longestStaticPrefix) const {
    return requireLValueHelper(*this, context, location, flags, longestStaticPrefix);
}

void RangeSelectExpression::getLongestStaticPrefixesImpl(
    SmallVector<std::pair<const ValueSymbol*, const Expression*>>& results,
    EvalContext& evalContext, const Expression* longestStaticPrefix) const {

    if (isConstantSelect(evalContext)) {
        if (!longestStaticPrefix)
            longestStaticPrefix = this;
    }
    else {
        longestStaticPrefix = nullptr;
    }

    value().getLongestStaticPrefixes(results, evalContext, longestStaticPrefix);
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
                                        const ASTContext& context) {
    auto sym = expr.getSymbolReference();
    if (!sym)
        return nullptr;

    // There is a built-in 'rand_mode' method that is present on every 'rand' and 'randc'
    // class property, and additionally on subelements of those properties.
    if (selector.name == "rand_mode"sv) {
        if (sym->getRandMode() == RandMode::None)
            return nullptr;

        return CallExpression::fromBuiltInMethod(compilation, SymbolKind::ClassProperty, expr,
                                                 selector.name, invocation, withClause, context);
    }

    return CallExpression::fromBuiltInMethod(compilation, sym->kind, expr, selector.name,
                                             invocation, withClause, context);
}

Expression& MemberAccessExpression::fromSelector(
    Compilation& compilation, Expression& expr, const LookupResult::MemberSelector& selector,
    const InvocationExpressionSyntax* invocation,
    const ArrayOrRandomizeMethodExpressionSyntax* withClause, const ASTContext& context,
    bool isFromLookupChain) {

    // If the selector name is invalid just give up early.
    if (selector.name.empty())
        return badExpr(compilation, &expr);

    // The source range of the entire member access starts from the value being selected.
    SourceRange range{expr.sourceRange.start(), selector.nameRange.end()};

    // Special cases for built-in iterator methods that don't cleanly fit the general
    // mold of looking up members via the type of the expression.
    if (expr.kind == ExpressionKind::NamedValue) {
        auto& sym = expr.as<NamedValueExpression>().symbol;
        auto symKind = sym.kind;
        if (symKind == SymbolKind::Iterator) {
            auto& iter = sym.as<IteratorSymbol>();
            if (iter.indexMethodName == selector.name) {
                auto result = CallExpression::fromBuiltInMethod(compilation, symKind, expr,
                                                                "index"sv, invocation, withClause,
                                                                context);
                if (result)
                    return *result;
            }
        }
    }
    else if (expr.kind == ExpressionKind::Call && isFromLookupChain) {
        // It's an error to dot select from a call expression that
        // doesn't include parentheses, which it doesn't iff
        // isFromLookupChain is set.
        context.addDiag(diag::ChainedMethodParens, range);
    }

    auto errorIfNotProcedural = [&] {
        if (context.flags.has(ASTFlags::NonProcedural)) {
            context.addDiag(diag::DynamicNotProcedural, range);
            return true;
        }
        return false;
    };
    auto errorIfAssertion = [&] {
        if (context.flags.has(ASTFlags::AssertionExpr)) {
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
            scope = &type.as<Scope>();
            break;
        case SymbolKind::ClassType: {
            auto& ct = type.as<ClassType>();
            if (auto base = ct.getBaseClass(); base && base->isError())
                return badExpr(compilation, &expr);

            scope = &ct;
            break;
        }
        case SymbolKind::CovergroupType:
            scope = &type.as<CovergroupType>().getBody();
            break;
        case SymbolKind::EnumType:
        case SymbolKind::StringType:
        case SymbolKind::FixedSizeUnpackedArrayType:
        case SymbolKind::DynamicArrayType:
        case SymbolKind::AssociativeArrayType:
        case SymbolKind::QueueType:
        case SymbolKind::EventType:
        case SymbolKind::SequenceType: {
            if (auto result = tryBindSpecialMethod(compilation, expr, selector, invocation,
                                                   withClause, context)) {
                return *result;
            }

            return CallExpression::fromSystemMethod(compilation, expr, selector, invocation,
                                                    withClause, context);
        }
        case SymbolKind::ErrorType:
            return badExpr(compilation, &expr);
        case SymbolKind::VoidType:
            if (auto sym = expr.getSymbolReference()) {
                if (sym->kind == SymbolKind::Coverpoint) {
                    scope = &sym->as<CoverpointSymbol>();
                    break;
                }
                else if (sym->kind == SymbolKind::CoverCross) {
                    scope = &sym->as<CoverCrossSymbol>();
                    break;
                }
            }
            [[fallthrough]];
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
                                                                range);
        }
        case SymbolKind::ClassProperty: {
            Lookup::ensureVisible(*member, context, selector.nameRange);
            auto& prop = member->as<ClassPropertySymbol>();
            if (prop.lifetime == VariableLifetime::Automatic &&
                (errorIfNotProcedural() || errorIfAssertion())) {
                return badExpr(compilation, &expr);
            }

            return *compilation.emplace<MemberAccessExpression>(prop.getType(), expr, prop, range);
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
        case SymbolKind::Coverpoint:
        case SymbolKind::CoverCross:
        case SymbolKind::CoverageBin: {
            if (errorIfNotProcedural())
                return badExpr(compilation, &expr);
            return *compilation.emplace<MemberAccessExpression>(compilation.getVoidType(), expr,
                                                                *member, range);
        }
        case SymbolKind::EnumValue:
            // The thing being selected from doesn't actually matter, since the
            // enum value is a constant.
            return ValueExpressionBase::fromSymbol(context, *member, nullptr, range);
        default: {
            if (member->isValue()) {
                auto& value = member->as<ValueSymbol>();
                return *compilation.emplace<MemberAccessExpression>(value.getType(), expr, value,
                                                                    range);
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
    const ArrayOrRandomizeMethodExpressionSyntax* withClause, const ASTContext& context) {

    auto name = syntax.name.valueText();
    Expression& lhs = selfDetermined(compilation, *syntax.left, context);
    if (lhs.bad() || name.empty())
        return badExpr(compilation, &lhs);

    LookupResult::MemberSelector selector;
    selector.name = name;
    selector.dotLocation = syntax.dot.location();
    selector.nameRange = syntax.name.range();

    auto& result = fromSelector(compilation, lhs, selector, invocation, withClause, context,
                                /* isFromLookupChain */ false);

    if (result.kind != ExpressionKind::Call && !result.bad()) {
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
            auto fields = curr.type->getCanonicalType().as<UnpackedStructType>().fields;
            curr.fieldIt = fields.begin();
            curr.fieldEnd = fields.end();
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

        if (!(*curr.fieldIt)->getType().isEquivalent(targetType))
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
            stack.pop_back();

            curr.next();
            prepNext();
        }
        else {
            auto& type = (*curr.fieldIt)->getType();
            if (type.isUnpackedStruct()) {
                stack.emplace_back(curr);

                auto fields = type.getCanonicalType().as<UnpackedStructType>().fields;
                curr.type = &type;
                curr.val = &curr.val->at(curr.valIndex);
                curr.fieldIt = fields.begin();
                curr.fieldEnd = fields.end();
                curr.valIndex = 0;
                prepNext();
            }
        }
    }

    using FieldIt = std::span<const FieldSymbol* const>::iterator;

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
    SmallVector<State, 4> stack;
};

static bool translateUnionMembers(ConstantValue& result, const Type& targetType,
                                  RecursiveStructMemberIterator& rsmi) {
    // If the target type is still an unpacked struct then recurse deeper until we
    // reach a non-struct member that can be assigned a value.
    if (targetType.isUnpackedStruct()) {
        size_t i = 0;
        for (auto field : targetType.as<UnpackedStructType>().fields) {
            if (!translateUnionMembers(result.at(i++), field->getType().getCanonicalType(), rsmi)) {
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
                                std::string_view memberName) {
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

    auto& field = member.as<FieldSymbol>();
    auto& valueType = value().type->getCanonicalType();
    if (valueType.isUnpackedStruct()) {
        return cv.elements()[field.fieldIndex];
    }
    else if (valueType.isUnpackedUnion()) {
        auto& unionVal = cv.unionVal();
        if (unionVal->activeMember == field.fieldIndex)
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
        if (!checkPackedUnionTag(valueType, cvi, field.fieldIndex, context, sourceRange,
                                 member.name)) {
            return nullptr;
        }

        return cvi.slice(int32_t(type->getBitWidth() - 1), 0);
    }
    else {
        int32_t io = (int32_t)field.bitOffset;
        int32_t width = (int32_t)type->getBitWidth();
        cv = cv.integer().slice(width + io - 1, io);

        // Make sure sign and four-statedness are correct.
        return cv.convertToInt(type->getBitWidth(), type->isSigned(), type->isFourState());
    }
}

LValue MemberAccessExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    if (!lval)
        return nullptr;

    auto& field = member.as<FieldSymbol>();
    auto& valueType = value().type->getCanonicalType();
    if (valueType.isUnpackedStruct()) {
        lval.addIndex((int32_t)field.fieldIndex, nullptr);
    }
    else if (valueType.isUnpackedUnion()) {
        if (valueType.isTaggedUnion()) {
            auto target = lval.resolve();
            SLANG_ASSERT(target);

            if (target->unionVal()->activeMember != field.fieldIndex) {
                context.addDiag(diag::ConstEvalTaggedUnion, sourceRange) << member.name;
                return nullptr;
            }
        }
        lval.addIndex((int32_t)field.fieldIndex, type->getDefaultValue());
    }
    else if (valueType.isPackedUnion()) {
        auto cv = lval.load();
        if (!checkPackedUnionTag(valueType, cv.integer(), field.fieldIndex, context, sourceRange,
                                 member.name)) {
            return nullptr;
        }

        int32_t width = (int32_t)type->getBitWidth();
        lval.addBitSlice({width - 1, 0});
    }
    else {
        int32_t io = (int32_t)field.bitOffset;
        int32_t width = (int32_t)type->getBitWidth();
        lval.addBitSlice({width + io - 1, io});
    }

    return lval;
}

static bool isWithinCovergroup(const Symbol& field, const Scope& usageScope) {
    const Scope* scope = field.getParentScope();
    while (scope) {
        switch (scope->asSymbol().kind) {
            case SymbolKind::CovergroupType:
            case SymbolKind::CovergroupBody:
            case SymbolKind::Coverpoint:
            case SymbolKind::CoverCross:
                return scope == &usageScope;
            default:
                scope = scope->asSymbol().getParentScope();
                break;
        }
    }
    return false;
}

bool MemberAccessExpression::requireLValueImpl(const ASTContext& context, SourceLocation location,
                                               bitmask<AssignFlags> flags,
                                               const Expression* longestStaticPrefix) const {
    // If this is a selection of a class or covergroup member, assignability depends only
    // on the selected member and not on the handle itself. Otherwise, the opposite is true.
    auto& valueType = value().type->getCanonicalType();
    if (valueType.isClass() || valueType.isCovergroup() || valueType.isVoid()) {
        if (VariableSymbol::isKind(member.kind)) {
            if (!longestStaticPrefix)
                longestStaticPrefix = this;

            auto& var = member.as<VariableSymbol>();
            context.addDriver(var, *longestStaticPrefix, flags);

            return ValueExpressionBase::checkVariableAssignment(context,
                                                                member.as<VariableSymbol>(), flags,
                                                                location, sourceRange);
        }

        if (!location)
            location = sourceRange.start();

        auto& diag = context.addDiag(diag::ExpressionNotAssignable, location);
        diag.addNote(diag::NoteDeclarationHere, member.location);
        diag << sourceRange;
        return false;
    }

    if (VariableSymbol::isKind(member.kind) &&
        member.as<VariableSymbol>().flags.has(VariableFlags::ImmutableCoverageOption) &&
        !isWithinCovergroup(member, *context.scope)) {
        context.addDiag(diag::CoverOptionImmutable, location) << member.name;
        return false;
    }

    if (auto sym = value().getSymbolReference(); sym && sym->kind == SymbolKind::Net) {
        auto& net = sym->as<NetSymbol>();
        if (net.netType.netKind == NetType::UserDefined)
            context.addDiag(diag::UserDefPartialDriver, sourceRange) << net.name;
    }

    if (!longestStaticPrefix)
        longestStaticPrefix = this;

    return value().requireLValue(context, location, flags, longestStaticPrefix);
}

void MemberAccessExpression::getLongestStaticPrefixesImpl(
    SmallVector<std::pair<const ValueSymbol*, const Expression*>>& results,
    EvalContext& evalContext, const Expression* longestStaticPrefix) const {

    if (!longestStaticPrefix)
        longestStaticPrefix = this;
    return value().getLongestStaticPrefixes(results, evalContext, longestStaticPrefix);
}

void MemberAccessExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.writeLink("member", member);
    serializer.write("value", value());
}

} // namespace slang::ast
