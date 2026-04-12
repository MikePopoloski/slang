//------------------------------------------------------------------------------
// ValuePath.cpp
// A path to some subset of a value symbol
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/ValuePath.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/TypeProvider.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/FormatBuffer.h"

namespace slang::ast {

static bool isPartOfPath(ExpressionKind kind) {
    switch (kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
        case ExpressionKind::Call:
        case ExpressionKind::Concatenation:
        case ExpressionKind::ElementSelect:
        case ExpressionKind::RangeSelect:
        case ExpressionKind::MemberAccess:
            return true;
        default:
            return false;
    }
}

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

using BitRange = std::pair<uint64_t, uint64_t>;

static std::optional<BitRange> computeBounds(SmallVector<const Expression*>& path, size_t skip,
                                             EvalContext& evalContext, const Type& rootType) {
    auto type = &rootType.getCanonicalType();
    BitRange result{0, type->getSelectableWidth() - 1};

    for (size_t i = path.size() - skip; i > 0; i--) {
        uint64_t start, width;
        auto& elem = *path[i - 1];
        if (elem.kind == ExpressionKind::MemberAccess) {
            auto& member = elem.as<MemberAccessExpression>().member;
            if (member.kind != SymbolKind::Field)
                return std::nullopt;

            auto& field = member.as<FieldSymbol>();
            start = field.bitOffset;
            width = elem.type->getSelectableWidth();
        }
        else {
            auto elemRange = elem.evalSelector(evalContext, /* enforceBounds */ true);
            if (!elemRange)
                return std::nullopt;

            SLANG_ASSERT(elemRange->left >= 0 && elemRange->right >= 0);
            start = (uint64_t)elemRange->lower();
            width = elemRange->width();
        }

        if (type->kind == SymbolKind::FixedSizeUnpackedArrayType) {
            // Unpacked arrays need their selection adjusted since they
            // return a simple index instead of a bit offset.
            type = &type->getArrayElementType()->getCanonicalType();
            uint64_t elemWidth = type->getSelectableWidth();
            result.first += start * elemWidth;
            result.second = result.first + elemWidth - 1;
        }
        else {
            type = &elem.type->getCanonicalType();
            result.first += start;
            result.second = result.first + width - 1;
        }
    }

    return result;
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

        // if we're skipping selectors we should exit early because
        // we will never want to see anything further.
        if (skipSelectors)
            return;

        for (auto& elem : path) {
            switch (elem.kind) {
                case ExpressionKind::NamedValue:
                case ExpressionKind::HierarchicalValue:
                    break;
                case ExpressionKind::Call:
                case ExpressionKind::Concatenation:
                    visit(elem);
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
                    SLANG_UNREACHABLE;
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
    if (!isPartOfPath(unwrapped.kind))
        return;

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
                // This is the root.
                rootType = elem.type;
                rootSymbol = &elem.as<ValueExpressionBase>().symbol;

                // If we reached a root named value without having a static prefix,
                // this reference *is* the static prefix.
                if (!lsp)
                    lsp = &elem;
                break;
            case ExpressionKind::Call:
            case ExpressionKind::Concatenation:
                // This is the root but we have no LSP.
                rootType = elem.type;
                lsp = nullptr;
                break;
            case ExpressionKind::ElementSelect:
                noteSelect(elem, elem.as<ElementSelectExpression>().isConstantSelect(evalContext));
                break;
            case ExpressionKind::RangeSelect:
                noteSelect(elem, elem.as<RangeSelectExpression>().isConstantSelect(evalContext));
                break;
            case ExpressionKind::MemberAccess: {
                // It's possible this is an access to a static class member,
                // in which case this is actually the root of the path.
                auto& mae = elem.as<MemberAccessExpression>();
                if (auto prop = mae.member.as_if<ClassPropertySymbol>();
                    prop && prop->lifetime == VariableLifetime::Static) {
                    rootType = elem.type;
                    rootSymbol = prop;
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
                SLANG_UNREACHABLE;
        }
    }

    SLANG_ASSERT(rootType);
    if (lsp) {
        auto bounds = computeBounds(path, 0, evalContext, *rootType);
        if (bounds)
            lspBounds = *bounds;
        else
            lsp = nullptr;
    }
}

void ValuePath::visitPaths(const Expression& expr, EvalContext& evalContext,
                           function_ref<void(const ValuePath&)> callback, bool skipSelectors) {
    PathVisitor visitor(evalContext, callback, skipSelectors);
    expr.visit(visitor);
}

ValuePath ValuePath::shrinkToLSP() const {
    ValuePath result;
    result.fullExpr = lsp;
    result.lsp = lsp;
    result.lspBounds = lspBounds;
    if (result.fullExpr) {
        result.rootSymbol = rootSymbol;
        result.rootType = rootType;
    }
    return result;
}

static const Expression& doClone(BumpAllocator& alloc, const Expression& expr,
                                 EvalContext& evalContext) {
    auto evalInt = [&](const Expression& e) -> std::optional<int32_t> {
        if (auto cv = e.eval(evalContext); cv.isInteger())
            return cv.integer().as<int32_t>();
        return std::nullopt;
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
                                                           ese.selector(), expr.sourceRange);
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
            return *alloc.emplace<RangeSelectExpression>(rse.getSelectionKind(), *expr.type,
                                                         const_cast<Expression&>(newVal),
                                                         rse.left(), rse.right(), expr.sourceRange);
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

    auto& newExpr = doRetarget(alloc, *fullExpr, target);
    if (isFullyStatic()) {
        ValuePath result = *this;
        result.lsp = result.fullExpr = &newExpr;
        return result;
    }

    // We have dynamic components, so recompute the lsp properly.
    return ValuePath(newExpr, evalContext);
}

bool ValuePath::overlaps(const ValuePath& other) const {
    if (empty() || other.empty())
        return empty() && other.empty();

    if (rootSymbol != other.rootSymbol)
        return false;

    if (lsp && other.lsp) {
        if (lspBounds.first > other.lspBounds.second || lspBounds.second < other.lspBounds.first)
            return false;

        if (isFullyStatic() && other.isFullyStatic())
            return true;
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

} // namespace slang::ast
