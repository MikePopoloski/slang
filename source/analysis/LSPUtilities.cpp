//------------------------------------------------------------------------------
// LSPUtilities.cpp
// Helpers for longest static prefix (LSP) analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/LSPUtilities.h"

#include "slang/ast/expressions/ConversionExpression.h"

namespace slang::analysis {

using namespace ast;

void stringifyLSP(const Expression& expr, EvalContext& evalContext, FormatBuffer& buffer) {
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
        default:
            // Reachable via things like call().foo = 1;
            break;
    }
}

} // namespace slang::analysis
