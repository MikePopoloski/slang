//------------------------------------------------------------------------------
// ValuePath.cpp
// A path to some subset of a value symbol
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/ValuePath.h"

#include "../text/FormatBuffer.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/TypeProvider.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

static bool isSelectExpr(ExpressionKind kind) {
    switch (kind) {
        case ExpressionKind::ElementSelect:
        case ExpressionKind::RangeSelect:
        case ExpressionKind::MemberAccess:
            return true;
        default:
            return false;
    }
}

static bool isStaticProp(const Symbol& symbol) {
    return symbol.kind == SymbolKind::ClassProperty &&
           symbol.as<ClassPropertySymbol>().lifetime == VariableLifetime::Static;
}

// An index into an array without a fixed range is part of a static prefix if it
// is constant [11.5.3] and names an element the array can hold: an index that is
// known and not negative, or a key that is known.
static bool isElementIndex(const Type& arrayType, const Expression& index,
                           EvalContext& evalContext) {
    auto cv = index.eval(evalContext);
    if (!cv || cv.hasUnknown())
        return false;
    return arrayType.isAssociativeArray() || !cv.integer().isNegative();
}

static bool extendsPrefix(const ElementSelectExpression& expr, EvalContext& evalContext) {
    auto& valueType = *expr.value().type;
    if (!valueType.isDynamicallySizedArray())
        return expr.isConstantSelect(evalContext);
    return isElementIndex(valueType, expr.selector(), evalContext);
}

static bool extendsPrefix(const RangeSelectExpression& expr, EvalContext& evalContext) {
    auto& valueType = *expr.value().type;
    if (!valueType.isDynamicallySizedArray())
        return expr.isConstantSelect(evalContext);
    return isElementIndex(valueType, expr.left(), evalContext) &&
           isElementIndex(valueType, expr.right(), evalContext);
}

using BitRange = std::pair<uint64_t, uint64_t>;

// Computes the bits that the selects in @a path cover, walking them from the root
// outward. A select into the elements of a dynamically sized array leaves the storage
// that holds the array: @a onElements is told the bits of the array there and the key
// selected, which is empty except for an associative array, and the walk goes on in
// the storage of those elements, which is laid out by index like an unpacked array.
template<typename TOnElements>
static std::optional<BitRange> computeBounds(SmallVector<const Expression*>& path, size_t skip,
                                             EvalContext& evalContext, const Type& rootType,
                                             TOnElements&& onElements) {
    auto type = &rootType.getCanonicalType();
    BitRange result{0, type->getSelectableWidth() - 1};

    for (size_t i = path.size() - skip; i > 0; i--) {
        uint64_t start, width;
        auto& elem = *path[i - 1];
        const bool isAssociative = type->kind == SymbolKind::AssociativeArrayType;
        const bool isDynamicallySized = isAssociative ||
                                        type->kind == SymbolKind::DynamicArrayType ||
                                        type->kind == SymbolKind::QueueType;
        if (elem.kind == ExpressionKind::MemberAccess) {
            auto& member = elem.as<MemberAccessExpression>().member;
            if (member.kind != SymbolKind::Field)
                return std::nullopt;

            auto& field = member.as<FieldSymbol>();
            start = field.bitOffset;
            width = elem.type->getSelectableWidth();
        }
        else if (isAssociative) {
            auto key = elem.as<ElementSelectExpression>().selector().eval(evalContext);
            if (!key || key.hasUnknown())
                return std::nullopt;

            // Each key's element is a unit of storage of its own.
            onElements(result, std::move(key));
            result = {0, 0};
            start = 0;
            width = 1;
        }
        else {
            auto elemRange = elem.evalSelector(evalContext, /* enforceBounds */ true);
            if (!elemRange)
                return std::nullopt;

            SLANG_ASSERT(elemRange->left >= 0 && elemRange->right >= 0);
            start = (uint64_t)elemRange->lower();
            width = elemRange->width();

            if (isDynamicallySized) {
                onElements(result, ConstantValue());
                result = {0, 0};
            }
        }

        if (type->kind == SymbolKind::FixedSizeUnpackedArrayType || isDynamicallySized) {
            // Unpacked arrays need their selection adjusted since they
            // return a simple index instead of a bit offset. A range select
            // covers `width` elements, not only the first one.
            uint64_t elemWidth = type->getArrayElementType()->getSelectableWidth();
            type = &elem.type->getCanonicalType();
            result.first += start * elemWidth;
            result.second = result.first + width * elemWidth - 1;
        }
        else {
            type = &elem.type->getCanonicalType();
            result.first += start;
            result.second = result.first + width - 1;
        }
    }

    return result;
}

// For selects known to stay in the storage that holds the root, such as those
// of a packed type, which holds no dynamically sized array.
static std::optional<BitRange> computeBounds(SmallVector<const Expression*>& path, size_t skip,
                                             EvalContext& evalContext, const Type& rootType) {
    return computeBounds(path, skip, evalContext, rootType,
                         [](const BitRange&, ConstantValue&&) { SLANG_UNREACHABLE; });
}

template<typename T>
concept IsSelectExpr =
    IsAnyOf<T, ElementSelectExpression, RangeSelectExpression, MemberAccessExpression,
            HierarchicalValueExpression, NamedValueExpression>;

struct PathVisitor {
    EvalContext& evalCtx;
    function_ref<void(const ValuePath&)> cb;
    bool skipSelectors;

    PathVisitor(EvalContext& evalCtx, function_ref<void(const ValuePath&)> cb, bool skipSelectors) :
        evalCtx(evalCtx), cb(cb), skipSelectors(skipSelectors) {}

    template<typename T>
        requires(std::is_base_of_v<Expression, T> && !IsSelectExpr<T>)
    void visit(const T& expr) {
        if constexpr (std::is_same_v<T, Expression>) {
            // We don't have a concrete type, we need to dispatch.
            expr.visit(*this);
        }
        else if constexpr (requires { expr.visitExprs(*this); }) {
            expr.visitExprs(*this);
        }
    }

    template<typename T>
        requires(IsSelectExpr<T>)
    void visit(const T& expr) {
        ValuePath path(expr, evalCtx);
        cb(path);

        if (skipSelectors) {
            SLANG_ASSERT(path.rootExpr);
            SLANG_ASSERT(!isSelectExpr(path.rootExpr->kind));
            if (!ValueExpressionBase::isKind(path.rootExpr->kind)) {
                visit(*path.rootExpr);
            }
            return;
        }

        for (auto& elem : path) {
            switch (elem.kind) {
                case ExpressionKind::NamedValue:
                case ExpressionKind::HierarchicalValue:
                    break;
                case ExpressionKind::ElementSelect:
                    visit(elem.as<ElementSelectExpression>().selector());
                    break;
                case ExpressionKind::RangeSelect: {
                    auto& rs = elem.as<RangeSelectExpression>();
                    visit(rs.left());
                    visit(rs.right());
                    break;
                }
                case ExpressionKind::MemberAccess: {
                    // If this is a static property it's the end of the path but we
                    // want to keep going anyway to visit other selectors.
                    auto& mae = elem.as<MemberAccessExpression>();
                    if (isStaticProp(mae.member))
                        visit(mae.value());
                    break;
                }
                default:
                    visit(elem);
                    break;
            }
        }
    }

    void visit(const Pattern&) {}
    void visit(const TimingControl&) {}
    void visit(const Constraint&) {}
    void visit(const AssertionExpr&) {}
};

ValuePath::ValuePath(const Expression& initialExpr, EvalContext& evalContext) {
    // Conversions are not part of a value path but we look through
    // them here during construction for convenience.
    auto& unwrapped = initialExpr.unwrapImplicitConversions();
    fullExpr = &unwrapped;

    SmallVector<const Expression*> path;
    auto noteSelect = [&](const Expression& expr, bool isConst) {
        if (isConst) {
            if (!lsp)
                lsp = &expr;
            path.push_back(&expr);
        }
        else {
            lsp = nullptr;
            path.clear();
        }
    };

    for (auto& elem : *this) {
        switch (elem.kind) {
            case ExpressionKind::NamedValue:
            case ExpressionKind::HierarchicalValue:
                // If we reached a root named value without having a static prefix,
                // this reference *is* the static prefix.
                rootExpr = &elem;
                if (!lsp)
                    lsp = &elem;
                break;
            case ExpressionKind::ElementSelect:
                noteSelect(elem, extendsPrefix(elem.as<ElementSelectExpression>(), evalContext));
                break;
            case ExpressionKind::RangeSelect:
                noteSelect(elem, extendsPrefix(elem.as<RangeSelectExpression>(), evalContext));
                break;
            case ExpressionKind::MemberAccess: {
                // It's possible this is an access to a static class member,
                // in which case this is actually the root of the path.
                auto& mae = elem.as<MemberAccessExpression>();
                if (isStaticProp(mae.member)) {
                    rootExpr = &elem;
                    if (!lsp)
                        lsp = &elem;
                }
                else {
                    auto& valueType = mae.value().type->getCanonicalType();
                    noteSelect(elem, !valueType.isObjectHandleType() && !valueType.isVoid());
                }
                break;
            }
            default:
                // This is the root but we have no LSP.
                rootExpr = &elem;
                lsp = nullptr;
                break;
        }
    }

    SLANG_ASSERT(rootExpr);
    if (lsp) {
        SLANG_ASSERT(rootSymbol());

        std::optional<BitRange> firstArray;
        auto bounds = computeBounds(path, 0, evalContext, *rootExpr->type,
                                    [&](const BitRange& arrayBounds, ConstantValue&&) {
                                        if (!firstArray)
                                            firstArray = arrayBounds;
                                    });
        if (bounds)
            lspBounds = firstArray.value_or(*bounds);
        else
            lsp = nullptr;
    }
}

// Gets the array that @a expr selects elements of, if it is a select into the
// elements of a dynamically sized array.
static const Expression* getSelectedArray(const Expression& expr) {
    const Expression* value;
    switch (expr.kind) {
        case ExpressionKind::ElementSelect:
            value = &expr.as<ElementSelectExpression>().value();
            break;
        case ExpressionKind::RangeSelect:
            value = &expr.as<RangeSelectExpression>().value();
            break;
        default:
            return nullptr;
    }
    return value->type->isDynamicallySizedArray() ? value : nullptr;
}

bool ValuePath::selectsIntoElements() const {
    // A packed root holds no dynamically sized array.
    if (rootExpr->type->isIntegral())
        return false;

    for (auto it = iterator(lsp); it != end(); ++it) {
        if (getSelectedArray(*it))
            return true;
    }
    return false;
}

const Expression& ValuePath::getFixedLayoutPrefix(const Expression& lsp) {
    // Walking from the outermost select toward the root, the last array whose
    // elements are selected is the first one entered from the root.
    const Expression* result = &lsp;
    for (auto it = iterator(&lsp); it != iterator(); ++it) {
        if (auto array = getSelectedArray(*it))
            result = array;
    }
    return *result;
}

StoragePlace ValuePath::getLSPPlace(
    EvalContext& evalContext,
    function_ref<const ElementStorage&(ElementStorage&&)> keepElements) const {
    auto& symbol = *rootSymbol();
    StoragePlace place{StorageLocation(symbol), lspBounds};

    // The selects of the prefix, outermost first, leaving out the root.
    SmallVector<const Expression*> components;
    for (auto it = iterator(lsp); it != end(); ++it)
        components.push_back(&*it);
    components.pop_back();

    ElementStorage elements{&symbol, {}};
    auto bounds = computeBounds(components, 0, evalContext, *rootExpr->type,
                                [&](const BitRange& arrayBounds, ConstantValue&& key) {
                                    elements.steps.push_back({arrayBounds.first, std::move(key)});
                                });

    // A key that does not evaluate here leaves the place as the array as a whole.
    if (bounds) {
        place.location = StorageLocation(keepElements(std::move(elements)));
        place.bitRange = *bounds;
    }
    return place;
}

void ValuePath::visitPaths(const Expression& expr, EvalContext& evalContext,
                           function_ref<void(const ValuePath&)> callback, bool skipSelectors) {
    PathVisitor visitor(evalContext, callback, skipSelectors);
    expr.visit(visitor);
}

const ValueSymbol* ValuePath::rootSymbol() const {
    if (rootExpr) {
        switch (rootExpr->kind) {
            case ExpressionKind::NamedValue:
            case ExpressionKind::HierarchicalValue:
                return &rootExpr->as<ValueExpressionBase>().symbol;
            case ExpressionKind::MemberAccess:
                return &rootExpr->as<MemberAccessExpression>().member.as<ClassPropertySymbol>();
            default:
                break;
        }
    }
    return nullptr;
}

static const Expression& doClone(BumpAllocator& alloc, const Expression& expr,
                                 EvalContext& evalContext) {
    auto evalInt = [&](const Expression& e) -> std::optional<int32_t> {
        if (auto cv = e.eval(evalContext); cv.isInteger())
            return cv.integer().as<int32_t>();
        return std::nullopt;
    };

    // A selector into an array without a fixed range is replaced by the integer it
    // evaluates to, if any, so that the element it names stays known outside this
    // evaluation context.
    auto bake = [&](const Expression& array, const Expression& e) -> const Expression& {
        if (array.type->hasFixedRange())
            return e;

        if (auto cv = e.eval(evalContext); cv.isInteger()) {
            return *alloc.emplace<IntegerLiteral>(alloc, *e.type, cv.integer(),
                                                  /* isDeclaredUnsized */ false, e.sourceRange);
        }
        return e;
    };

    switch (expr.kind) {
        case ExpressionKind::ElementSelect: {
            auto& ese = expr.as<ElementSelectExpression>();
            auto& newVal = doClone(alloc, ese.value(), evalContext);
            if (ese.value().type->hasFixedRange()) {
                if (auto intVal = evalInt(ese.selector())) {
                    auto& result = ElementSelectExpression::fromConstant(
                        alloc, const_cast<Expression&>(newVal), *intVal, evalContext.astCtx);
                    result.sourceRange = expr.sourceRange;
                    return result;
                }
            }
            return *alloc.emplace<ElementSelectExpression>(*expr.type,
                                                           const_cast<Expression&>(newVal),
                                                           bake(ese.value(), ese.selector()),
                                                           expr.sourceRange);
        }
        case ExpressionKind::RangeSelect: {
            auto& rse = expr.as<RangeSelectExpression>();
            auto& newVal = doClone(alloc, rse.value(), evalContext);
            if (rse.value().type->hasFixedRange()) {
                auto left = evalInt(rse.left());
                auto right = evalInt(rse.right());
                if (left && right) {
                    auto& result = RangeSelectExpression::fromConstant(
                        alloc, const_cast<Expression&>(newVal), {*left, *right}, evalContext.astCtx,
                        rse.getSelectionKind());
                    result.sourceRange = expr.sourceRange;
                    return result;
                }
            }
            return *alloc.emplace<RangeSelectExpression>(
                rse.getSelectionKind(), *expr.type, const_cast<Expression&>(newVal),
                bake(rse.value(), rse.left()), bake(rse.value(), rse.right()), expr.sourceRange);
        }
        case ExpressionKind::MemberAccess: {
            auto& access = expr.as<MemberAccessExpression>();
            auto& newVal = doClone(alloc, access.value(), evalContext);
            return *alloc.emplace<MemberAccessExpression>(*expr.type,
                                                          const_cast<Expression&>(newVal),
                                                          access.member, expr.sourceRange);
        }
        default:
            // Just return the expression as-is, nothing to do here.
            return expr;
    }
}

ValuePath ValuePath::clone(BumpAllocator& alloc, EvalContext& evalContext) const {
    // Don't bother allocating anything if we don't have an lsp
    // or we do but it has no selects.
    if (!lsp || !isSelectExpr(lsp->kind))
        return *this;

    auto& clonedExpr = doClone(alloc, *fullExpr, evalContext);
    if (isFullyStatic()) {
        ValuePath result = *this;
        result.lsp = result.fullExpr = &clonedExpr;
        return result;
    }

    // We have dynamic components, so recompute the lsp properly.
    return ValuePath(clonedExpr, evalContext);
}

static const Expression& doRetarget(BumpAllocator& alloc, const Expression& expr,
                                    const ValueSymbol& target) {
    auto checkTypeMatch = [&](const Type& symType) {
        auto& targetType = target.getType();
        return symType.isMatching(targetType) || symType.isIdenticalStructUnion(targetType);
    };

    switch (expr.kind) {
        case ExpressionKind::ElementSelect: {
            auto& ese = expr.as<ElementSelectExpression>();
            auto& newVal = doRetarget(alloc, ese.value(), target);
            return *alloc.emplace<ElementSelectExpression>(*ese.type,
                                                           const_cast<Expression&>(newVal),
                                                           ese.selector(), ese.sourceRange);
        }
        case ExpressionKind::RangeSelect: {
            auto& rse = expr.as<RangeSelectExpression>();
            auto& newVal = doRetarget(alloc, rse.value(), target);
            return *alloc.emplace<RangeSelectExpression>(rse.getSelectionKind(), *rse.type,
                                                         const_cast<Expression&>(newVal),
                                                         rse.left(), rse.right(), rse.sourceRange);
        }
        case ExpressionKind::MemberAccess: {
            auto& access = expr.as<MemberAccessExpression>();
            if (isStaticProp(access.member)) {
                // This is actually the root, so replace it instead of descending deeper.
                // We're at the root; replace it and we're done.
                SLANG_ASSERT(checkTypeMatch(*expr.type));
                return *alloc.emplace<NamedValueExpression>(target, expr.sourceRange);
            }

            auto& newVal = doRetarget(alloc, access.value(), target);
            return *alloc.emplace<MemberAccessExpression>(*expr.type,
                                                          const_cast<Expression&>(newVal),
                                                          access.member, expr.sourceRange);
        }
        default:
            // We're at the root; replace it and we're done.
            SLANG_ASSERT(checkTypeMatch(*expr.type));
            return *alloc.emplace<NamedValueExpression>(target, expr.sourceRange);
    }
}

ValuePath ValuePath::retarget(BumpAllocator& alloc, EvalContext& evalContext,
                              const ValueSymbol& target) const {
    SLANG_ASSERT(!empty());
    return ValuePath(doRetarget(alloc, *fullExpr, target), evalContext);
}

bool ValuePath::overlaps(const ValuePath& other) const {
    if (empty() || other.empty())
        return false;

    if (rootSymbol() != other.rootSymbol())
        return false;

    if (lsp && other.lsp) {
        if (lspBounds.first > other.lspBounds.second || lspBounds.second < other.lspBounds.first)
            return false;

        // A prefix that goes on into the elements of a dynamically sized array
        // has the bits of the whole array, which don't tell which element it is.
        if (isFullyStatic() && other.isFullyStatic() && !isLSPInElements() &&
            !other.isLSPInElements()) {
            return true;
        }
    }

    return fullExpr->isEquivalentTo(*other.fullExpr);
}

static void doStringify(const Expression& expr, EvalContext& evalContext, FormatBuffer& buffer) {
    switch (expr.kind) {
        case ExpressionKind::ElementSelect: {
            auto& select = expr.as<ElementSelectExpression>();
            doStringify(select.value(), evalContext, buffer);
            if (auto cv = select.selector().eval(evalContext))
                buffer.format("[{}]", cv.toString());
            else {
                buffer.append("[");
                doStringify(select.selector(), evalContext, buffer);
                buffer.append("]");
            }
            break;
        }
        case ExpressionKind::RangeSelect: {
            auto& select = expr.as<RangeSelectExpression>();
            doStringify(select.value(), evalContext, buffer);

            auto left = select.left().eval(evalContext);
            auto right = select.right().eval(evalContext);
            auto rangeOp = SemanticFacts::getRangeSelectOpText(select.getSelectionKind());
            if (left && right)
                buffer.format("[{}{}{}]", left.toString(), rangeOp, right.toString());
            else {
                buffer.append("[");
                doStringify(select.left(), evalContext, buffer);
                buffer.append(rangeOp);
                doStringify(select.right(), evalContext, buffer);
                buffer.append("]");
            }
            break;
        }
        case ExpressionKind::MemberAccess: {
            auto& access = expr.as<MemberAccessExpression>();
            if (isStaticProp(access.member)) {
                buffer.format("{}::", access.value().type->toString());
            }
            else {
                doStringify(access.value(), evalContext, buffer);
                if (!buffer.empty())
                    buffer.append(".");
            }
            buffer.append(access.member.name);
            break;
        }
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
            buffer.append(expr.as<ValueExpressionBase>().symbol.name);
            break;
        case ExpressionKind::Concatenation: {
            auto& concat = expr.as<ConcatenationExpression>();
            if (!concat.operands().empty()) {
                buffer.append("{");
                for (auto op : concat.operands()) {
                    doStringify(*op, evalContext, buffer);
                    buffer.append(", ");
                }
                buffer.pop_back();
                buffer.pop_back();
                buffer.append("}");
            }
            break;
        }
        case ExpressionKind::Call: {
            auto& call = expr.as<CallExpression>();
            buffer.format("{}(", call.getSubroutineName());
            if (!call.arguments().empty()) {
                for (auto arg : call.arguments()) {
                    doStringify(*arg, evalContext, buffer);
                    buffer.append(", ");
                }
                buffer.pop_back();
                buffer.pop_back();
            }
            buffer.append(")");
            break;
        }
        default:
            if (expr.syntax)
                buffer.append(expr.syntax->toString());
            else
                buffer.append("...");
            break;
    }
}

std::string ValuePath::toString(EvalContext& evalContext) const {
    if (empty())
        return "";

    FormatBuffer buffer;
    doStringify(*fullExpr, evalContext, buffer);
    return buffer.str();
}

static void getComponents(const ValuePath& path, SmallVector<const Expression*>& components) {
    for (auto& elem : path)
        components.push_back(&elem);

    // Don't include the root.
    components.pop_back();
}

static Expression* glueConnExpr(BumpAllocator& alloc, EvalContext& evalContext, size_t startIndex,
                                Expression* expr, SmallVector<const Expression*>& lspPath) {
    // First, replicate all of the selects for unpacked types. The only way that
    // types can mismatch here is for fixed size arrays, which can have differing
    // ranges, so translate those along the way. A dynamically sized array is
    // indexed from zero or by key on both sides, so its selects carry over as they are.
    size_t index = startIndex;
    for (; index < lspPath.size(); index++) {
        auto& ct = expr->type->getCanonicalType();
        if (ct.isIntegral())
            break;

        auto elem = lspPath[lspPath.size() - 1 - index];
        if (elem->kind == ExpressionKind::MemberAccess) {
            auto& ma = elem->as<MemberAccessExpression>();
            expr = alloc.emplace<MemberAccessExpression>(*ma.type, *expr, ma.member,
                                                         ma.sourceRange);
            continue;
        }

        if (ct.isDynamicallySizedArray()) {
            if (elem->kind == ExpressionKind::ElementSelect) {
                auto& ese = elem->as<ElementSelectExpression>();
                expr = alloc.emplace<ElementSelectExpression>(*ese.type, *expr, ese.selector(),
                                                              expr->sourceRange);
            }
            else {
                auto& rse = elem->as<RangeSelectExpression>();
                expr = alloc.emplace<RangeSelectExpression>(rse.getSelectionKind(), *rse.type,
                                                            *expr, rse.left(), rse.right(),
                                                            expr->sourceRange);
            }
            continue;
        }

        auto targetDim = ct.getFixedRange();
        auto translateIndex = [&](int32_t index) {
            if (targetDim.isDescending())
                return targetDim.upper() - index;
            else
                return targetDim.lower() + index;
        };

        auto selection = elem->evalSelector(evalContext, /* enforceBounds */ true);
        SLANG_ASSERT(selection);

        selection->left = translateIndex(selection->left);
        selection->right = translateIndex(selection->right);

        if (elem->kind == ExpressionKind::ElementSelect) {
            expr = &ElementSelectExpression::fromConstant(alloc, *expr, selection->lower(),
                                                          evalContext.astCtx);
        }
        else {
            expr = &RangeSelectExpression::fromConstant(alloc, *expr, *selection,
                                                        evalContext.astCtx);
        }
    }

    // For remaining integral path components, compute the bounds and then
    // recreate a corresponding select tree that achieves those same bounds.
    if (index < lspPath.size()) {
        auto bounds = computeBounds(lspPath, index, evalContext, *expr->type);
        SLANG_ASSERT(bounds);

        // Note that this can't overflow here because it's a packed type
        // so the total width is bounded.
        ConstantRange range{int32_t(bounds->second), int32_t(bounds->first)};
        expr = &Expression::buildPackedSelectTree(alloc, *expr, range, evalContext.astCtx);
    }

    return expr;
}

static bool expandRefPortConn(BumpAllocator& alloc, EvalContext& evalContext, const ValuePath& path,
                              const Expression& externalConn, const Expression* internalConn,
                              function_ref<void(const ValuePath&)> callback) {
    if (externalConn.bad() || (internalConn && internalConn->bad()))
        return true;

    SmallVector<const Expression*> pathElems;
    getComponents(path, pathElems);

    size_t elemsToRemove = 0;
    if (internalConn) {
        SmallVector<const Expression*> internalPath;
        getComponents(ValuePath(*internalConn, evalContext), internalPath);

        // Remove the common prefix from the lsp path -- the remainder is the portion
        // of the expression that applies on top of the external connection. Note that
        // the paths are in reverse order so we need to walk backwards.
        while (elemsToRemove < internalPath.size() && elemsToRemove < pathElems.size()) {
            auto l = internalPath[internalPath.size() - 1 - elemsToRemove];
            auto r = pathElems[pathElems.size() - 1 - elemsToRemove];
            if (!l->isEquivalentTo(*r)) {
                // This port is not applicable because the internal connection
                // doesn't match the lsp and so assignments don't affect it.
                return false;
            }
            elemsToRemove++;
        }
    }

    if (elemsToRemove == pathElems.size()) {
        // The entire lsp is covered by the internal connection, so the external
        // connection is the relevant expression.
        ValuePath::visitPaths(externalConn, evalContext, callback, /* skipSelectors */ true);
    }
    else {
        // The external connection is only partially covered by the LSP. We need to
        // glue the uncovered portion of the LSP onto the external connection.
        // The const_cast here is okay because we never mutate anything during analysis.
        auto newExpr = glueConnExpr(alloc, evalContext, elemsToRemove,
                                    const_cast<Expression*>(&externalConn), pathElems);
        ValuePath::visitPaths(*newExpr, evalContext, callback, /* skipSelectors */ true);
    }
    return true;
}

static void expandModportConn(BumpAllocator& alloc, EvalContext& evalContext, const ValuePath& path,
                              const Expression& internalConn,
                              function_ref<void(const ValuePath&)> callback) {
    SmallVector<const Expression*> components;
    getComponents(path, components);

    // We need to glue the uncovered portion of the LSP onto the external connection.
    // The const_cast here is okay because we never mutate anything during analysis.
    auto newExpr = glueConnExpr(alloc, evalContext, 0, const_cast<Expression*>(&internalConn),
                                components);
    ValuePath::visitPaths(*newExpr, evalContext, callback, /* skipSelectors */ true);
}

void ValuePath::expandIndirectRefs(BumpAllocator& alloc, EvalContext& evalContext,
                                   function_ref<void(const ValuePath&)> callback) const {
    if (!lsp) {
        callback(*this);
        return;
    }

    auto symbol = rootSymbol();
    SLANG_ASSERT(symbol);

    if (auto mpp = symbol->as_if<ModportPortSymbol>()) {
        if (auto expr = mpp->getConnectionExpr(); expr && !expr->bad())
            expandModportConn(alloc, evalContext, *this, *expr, callback);
        return;
    }

    // If this symbol is connected to a ref port we need to chop off
    // the common part of the connection expression and glue the remainder
    // onto the target of the connection.
    bool anyRefPorts = false;
    for (auto backref = symbol->getFirstPortBackref(); backref;
         backref = backref->getNextBackreference()) {
        auto& port = *backref->port;
        if (port.direction == ArgumentDirection::Ref) {
            auto scope = symbol->getParentScope();
            SLANG_ASSERT(scope);

            auto inst = scope->asSymbol().as<InstanceBodySymbol>().parentInstance;
            SLANG_ASSERT(inst);

            if (auto conn = inst->getPortConnection(port)) {
                if (auto expr = conn->getExpression()) {
                    anyRefPorts |= expandRefPortConn(alloc, evalContext, *this, *expr,
                                                     port.getInternalExpr(), callback);
                }
            }
        }
    }

    if (!anyRefPorts) {
        // No ref ports or modports involved, so just invoke the callback directly.
        callback(*this);
    }
}

void ValuePath::iterator::increment() {
    switch (expr->kind) {
        case ExpressionKind::ElementSelect:
            expr = &expr->as<ElementSelectExpression>().value();
            break;
        case ExpressionKind::RangeSelect:
            expr = &expr->as<RangeSelectExpression>().value();
            break;
        case ExpressionKind::MemberAccess: {
            auto& mae = expr->as<MemberAccessExpression>();
            if (isStaticProp(mae.member))
                expr = nullptr;
            else
                expr = &mae.value();
            break;
        }
        default:
            expr = nullptr;
            break;
    }
}

size_t ElementStorage::Step::hash() const {
    size_t h = 0;
    hash_combine(h, arrayOffset, key.hash());
    return h;
}

size_t ElementStorage::hash() const {
    size_t h = 0;
    hash_combine(h, symbol.get());
    for (auto& step : steps)
        hash_combine(h, step.hash());
    return h;
}

} // namespace slang::ast
