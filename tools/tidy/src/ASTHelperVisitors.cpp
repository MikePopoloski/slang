// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"

std::optional<std::string_view> getIdentifier(const slang::ast::Expression& expr) {
    const slang::ast::Symbol* symbol = nullptr;
    if (slang::ast::MemberAccessExpression::isKind(expr.kind)) {
        auto& memberAccess = expr.as<slang::ast::MemberAccessExpression>();
        if (slang::ast::NamedValueExpression::isKind(memberAccess.value().kind))
            symbol = &memberAccess.value().as<slang::ast::NamedValueExpression>().symbol;
    }
    else {
        symbol = expr.getSymbolReference();
    }

    if (symbol) {
        return symbol->name;
    }
    return {};
}
