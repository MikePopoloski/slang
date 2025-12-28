//------------------------------------------------------------------------------
// LSPUtilities.cpp
// Helpers for longest static prefix (LSP) analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/LSPUtilities.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/TypeProvider.h"

namespace slang::ast {

void LSPUtilities::stringifyLSP(const Expression& expr, EvalContext& evalContext,
                                FormatBuffer& buffer) {
    switch (expr.kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
            buffer.append(expr.as<ValueExpressionBase>().symbol.name);
            break;
        case ExpressionKind::Conversion:
            stringifyLSP(expr.as<ConversionExpression>().operand(), evalContext, buffer);
            break;
        case ExpressionKind::ElementSelect: {
            auto& select = expr.as<ElementSelectExpression>();
            stringifyLSP(select.value(), evalContext, buffer);
            buffer.format("[{}]", select.selector().eval(evalContext).toString());
            break;
        }
        case ExpressionKind::RangeSelect: {
            auto& select = expr.as<RangeSelectExpression>();
            stringifyLSP(select.value(), evalContext, buffer);
            buffer.format("[{}:{}]", select.left().eval(evalContext).toString(),
                          select.right().eval(evalContext).toString());
            break;
        }
        case ExpressionKind::MemberAccess: {
            auto& access = expr.as<MemberAccessExpression>();
            stringifyLSP(access.value(), evalContext, buffer);
            if (!buffer.empty())
                buffer.append(".");
            buffer.append(access.member.name);
            break;
        }
        case ExpressionKind::Concatenation: {
            auto& concat = expr.as<ConcatenationExpression>();
            if (!concat.operands().empty()) {
                buffer.append("{");
                for (auto op : concat.operands()) {
                    stringifyLSP(*op, evalContext, buffer);
                    buffer.append(", ");
                }
                buffer.pop_back();
                buffer.pop_back();
                buffer.append("}");
            }
            break;
        }
        default:
            // Reachable via things like call().foo = 1;
            break;
    }
}

static std::optional<DriverBitRange> computeBounds(SmallVector<const Expression*>& path,
                                                   size_t skip, EvalContext& evalContext,
                                                   const Type& rootType) {
    auto type = &rootType.getCanonicalType();
    DriverBitRange result{0, type->getSelectableWidth() - 1};

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

std::optional<DriverBitRange> LSPUtilities::getBounds(const Expression& prefixExpression,
                                                      EvalContext& evalContext,
                                                      const Type& rootType) {
    SmallVector<const Expression*> path;
    visitComponents(prefixExpression, /* includeRoot */ false,
                    [&](const Expression& expr) { path.push_back(&expr); });

    return computeBounds(path, 0, evalContext, rootType);
}

static Expression* glueConnExpr(BumpAllocator& alloc, EvalContext& evalContext, size_t startIndex,
                                Expression* expr, SmallVector<const Expression*>& lspPath) {
    // First, replicate all of the selects for unpacked types. The only way that
    // types can mismatch here is for fixed size arrays, which can have differing
    // ranges, so translate those along the way.
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

        auto targetDim = ct.getFixedRange();
        auto translateIndex = [&](int32_t index) {
            if (targetDim.isLittleEndian())
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

static bool expandRefPortConn(BumpAllocator& alloc, EvalContext& evalContext, const Expression& lsp,
                              bool isLValue, const Expression& externalConn,
                              const Expression* internalConn, LSPUtilities::LSPCallback callback) {
    if (externalConn.bad() || (internalConn && internalConn->bad()))
        return true;

    SmallVector<const Expression*> lspPath;
    LSPUtilities::visitComponents(lsp, /* includeRoot */ false,
                                  [&](const Expression& expr) { lspPath.push_back(&expr); });

    size_t elemsToRemove = 0;
    if (internalConn) {
        SmallVector<const Expression*> internalPath;
        LSPUtilities::visitComponents(*internalConn, /* includeRoot */ false,
                                      [&](const Expression& expr) {
                                          internalPath.push_back(&expr);
                                      });

        // Remove the common prefix from the lsp path -- the remainder is the portion
        // of the expression that applies on top of the external connection. Note that
        // the paths are in reverse order so we need to walk backwards.
        while (elemsToRemove < internalPath.size() && elemsToRemove < lspPath.size()) {
            auto l = internalPath[internalPath.size() - 1 - elemsToRemove];
            auto r = lspPath[lspPath.size() - 1 - elemsToRemove];
            if (!l->isEquivalentTo(*r)) {
                // This port is not applicable because the internal connection
                // doesn't match the lsp and so assignments don't affect it.
                return false;
            }
            elemsToRemove++;
        }
    }

    if (elemsToRemove == lspPath.size()) {
        // The entire lsp is covered by the internal connection, so the external
        // connection is the relevant expression.
        LSPUtilities::visitLSPs(externalConn, evalContext, callback, isLValue);
    }
    else {
        // The external connection is only partially covered by the LSP. We need to
        // glue the uncovered portion of the LSP onto the external connection.
        // The const_cast here is okay because we never mutate anything during analysis.
        auto newExpr = glueConnExpr(alloc, evalContext, elemsToRemove,
                                    const_cast<Expression*>(&externalConn), lspPath);
        LSPUtilities::visitLSPs(*newExpr, evalContext, callback, isLValue);
    }
    return true;
}

static void expandModportConn(BumpAllocator& alloc, EvalContext& evalContext, const Expression& lsp,
                              bool isLValue, const Expression& internalConn,
                              LSPUtilities::LSPCallback callback) {
    SmallVector<const Expression*> lspPath;
    LSPUtilities::visitComponents(lsp, /* includeRoot */ false,
                                  [&](const Expression& expr) { lspPath.push_back(&expr); });

    // We need to glue the uncovered portion of the LSP onto the external connection.
    // The const_cast here is okay because we never mutate anything during analysis.
    auto newExpr = glueConnExpr(alloc, evalContext, 0, const_cast<Expression*>(&internalConn),
                                lspPath);
    LSPUtilities::visitLSPs(*newExpr, evalContext, callback, isLValue);
}

void LSPUtilities::expandIndirectLSPs(BumpAllocator& alloc, const Expression& expr,
                                      EvalContext& evalContext, LSPCallback callback,
                                      bool isLValue) {
    visitLSPs(
        expr, evalContext,
        [&](const ValueSymbol& symbol, const Expression& lsp, bool isLValue) {
            expandIndirectLSP(alloc, evalContext, callback, symbol, lsp, isLValue);
        },
        isLValue);
}

void LSPUtilities::expandIndirectLSP(BumpAllocator& alloc, EvalContext& evalContext,
                                     LSPCallback callback, const ValueSymbol& symbol,
                                     const Expression& lsp, bool isLValue) {
    if (symbol.kind == SymbolKind::ModportPort) {
        if (auto expr = symbol.as<ModportPortSymbol>().getConnectionExpr(); expr && !expr->bad())
            expandModportConn(alloc, evalContext, lsp, isLValue, *expr, callback);
        return;
    }

    // If this symbol is connected to a ref port we need to chop off
    // the common part of the connection expression and glue the remainder
    // onto the target of the connection.
    bool anyRefPorts = false;
    for (auto backref = symbol.getFirstPortBackref(); backref;
         backref = backref->getNextBackreference()) {
        auto& port = *backref->port;
        if (port.direction == ArgumentDirection::Ref) {
            auto scope = symbol.getParentScope();
            SLANG_ASSERT(scope);

            auto inst = scope->asSymbol().as<InstanceBodySymbol>().parentInstance;
            SLANG_ASSERT(inst);

            if (auto conn = inst->getPortConnection(port)) {
                if (auto expr = conn->getExpression()) {
                    anyRefPorts |= expandRefPortConn(alloc, evalContext, lsp, isLValue, *expr,
                                                     port.getInternalExpr(), callback);
                }
            }
        }
    }

    if (!anyRefPorts) {
        // No ref ports or modports involved, so just invoke the callback directly.
        callback(symbol, lsp, isLValue);
    }
}

const Expression& LSPUtilities::cloneLSP(BumpAllocator& alloc, const Expression& expr,
                                         EvalContext& evalContext) {
    auto evalInt = [&](const Expression& e) -> std::optional<int32_t> {
        if (auto cv = e.eval(evalContext); cv.isInteger())
            return cv.integer().as<int32_t>();
        return std::nullopt;
    };

    switch (expr.kind) {
        case ExpressionKind::ElementSelect: {
            auto& ese = expr.as<ElementSelectExpression>();
            if (auto intVal = evalInt(ese.selector())) {
                auto& newVal = cloneLSP(alloc, ese.value(), evalContext);
                auto& result = ElementSelectExpression::fromConstant(
                    alloc, const_cast<Expression&>(newVal), *intVal, evalContext.astCtx);
                result.sourceRange = expr.sourceRange;
                return result;
            }
            break;
        }
        case ExpressionKind::RangeSelect: {
            auto& rse = expr.as<RangeSelectExpression>();
            auto left = evalInt(rse.left());
            auto right = evalInt(rse.right());
            if (left && right) {
                auto& newVal = cloneLSP(alloc, rse.value(), evalContext);
                auto& result = RangeSelectExpression::fromConstant(
                    alloc, const_cast<Expression&>(newVal), {*left, *right}, evalContext.astCtx,
                    rse.getSelectionKind());
                result.sourceRange = expr.sourceRange;
                return result;
            }
            break;
        }
        case ExpressionKind::MemberAccess: {
            auto& access = expr.as<MemberAccessExpression>();
            auto& newVal = cloneLSP(alloc, access.value(), evalContext);
            return *alloc.emplace<MemberAccessExpression>(*expr.type,
                                                          const_cast<Expression&>(newVal),
                                                          access.member, expr.sourceRange);
        }
        default:
            break;
    }

    // Just return the expression as-is, nothing to do here.
    return expr;
}

const Expression& LSPUtilities::retargetLSP(BumpAllocator& alloc, const Expression& expr,
                                            const ValueSymbol& target) {
    switch (expr.kind) {
        case ExpressionKind::ElementSelect: {
            auto& ese = expr.as<ElementSelectExpression>();
            auto& newVal = retargetLSP(alloc, ese.value(), target);
            return *alloc.emplace<ElementSelectExpression>(*ese.type,
                                                           const_cast<Expression&>(newVal),
                                                           ese.selector(), ese.sourceRange);
        }
        case ExpressionKind::RangeSelect: {
            auto& rse = expr.as<RangeSelectExpression>();
            auto& newVal = retargetLSP(alloc, rse.value(), target);
            return *alloc.emplace<RangeSelectExpression>(rse.getSelectionKind(), *rse.type,
                                                         const_cast<Expression&>(newVal),
                                                         rse.left(), rse.right(), rse.sourceRange);
        }
        case ExpressionKind::MemberAccess: {
            auto& access = expr.as<MemberAccessExpression>();
            auto& newVal = retargetLSP(alloc, access.value(), target);
            return *alloc.emplace<MemberAccessExpression>(*expr.type,
                                                          const_cast<Expression&>(newVal),
                                                          access.member, expr.sourceRange);
        }
        case ExpressionKind::NamedValue: {
            auto& nve = expr.as<NamedValueExpression>();
            SLANG_ASSERT(nve.symbol.getType().isMatching(target.getType()));
            return *alloc.emplace<NamedValueExpression>(target, nve.sourceRange);
        }
        case ExpressionKind::HierarchicalValue: {
            auto& hve = expr.as<HierarchicalValueExpression>();
            SLANG_ASSERT(hve.symbol.getType().isMatching(target.getType()));

            auto ref = hve.ref;
            ref.target = &target;
            return *alloc.emplace<HierarchicalValueExpression>(target, ref, hve.sourceRange);
        }
        default:
            return expr;
    }
}

} // namespace slang::ast
