//------------------------------------------------------------------------------
// LSPUtilities.cpp
// Helpers for longest static prefix (LSP) analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/LSPUtilities.h"

#include "slang/ast/expressions/ConversionExpression.h"
#include "slang/ast/expressions/OperatorExpressions.h"

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

std::optional<DriverBitRange> LSPUtilities::getBounds(const Expression& prefixExpression,
                                                      EvalContext& evalContext,
                                                      const Type& rootType) {
    auto type = &rootType.getCanonicalType();
    DriverBitRange result{0, type->getSelectableWidth() - 1};

    SmallVector<const Expression*> path;
    visitComponents(prefixExpression, /* includeRoot */ false,
                    [&](const Expression& expr) { path.push_back(&expr); });

    for (size_t i = path.size(); i > 0; i--) {
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

} // namespace slang::ast
