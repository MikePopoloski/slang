// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"

#include "slang/syntax/AllSyntax.h"

std::optional<std::string_view> getIdentifier(const slang::ast::Expression& expr) {
    const slang::ast::Symbol* symbol = nullptr;
    if (slang::ast::MemberAccessExpression::isKind(expr.kind)) {
        auto& memberAccess = expr.as<slang::ast::MemberAccessExpression>();
        // Recursively get the base identifier from the value part of the member access
        return getIdentifier(memberAccess.value());
    }
    else {
        symbol = expr.getSymbolReference();
    }

    if (symbol) {
        return symbol->name;
    }
    return {};
}

std::optional<slang::SourceLocation> getExpressionSourceLocation(
    const slang::ast::Expression& expr) {
    if (!expr.syntax) {
        return std::nullopt;
    }
    return expr.syntax->getFirstToken().location();
}
