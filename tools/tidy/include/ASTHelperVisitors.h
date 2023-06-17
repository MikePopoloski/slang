//------------------------------------------------------------------------------
//! @file ASTHelperVisitors.h
//! @brief Reusable AST visitors
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "TidyConfig.h"
#include "TidyFactory.h"
#include <filesystem>

#include "slang/ast/ASTVisitor.h"

#define NEEDS_SKIP_SYMBOL(__symbol)         \
    if (skip((__symbol).location.bufferName)) \
        return;

#define NEEDS_SKIP_STATEMENT(__statement)               \
    if (skip(statement.sourceRange.start().bufferName)) \
        return;

struct TidyVisitor {
protected:
    explicit TidyVisitor(slang::Diagnostics& diagnostics) :
        diags(diagnostics), config(Registry::getConfig()) {}

    [[nodiscard]] bool skip(std::string_view path) const {
        auto file = std::filesystem::path(path).filename();
        const auto& skipFiles = config.getSkipFiles();
        return std::find(skipFiles.begin(), skipFiles.end(), file) != skipFiles.end();
    }

    slang::Diagnostics& diags;
    const TidyConfig& config;
};

/// ASTVisitor that will collect all identifiers under a node and store them in the identifiers
/// internal variable so they can be retrieved later
struct CollectIdentifiers : public slang::ast::ASTVisitor<CollectIdentifiers, false, true> {
    void handle(const slang::ast::NamedValueExpression& expression) {
        if (auto* symbol = expression.getSymbolReference(); symbol) {
            identifiers.push_back(symbol->name);
        }
    }
    std::vector<std::string_view> identifiers;
};

/// ASTVisitor that will try to find the provided name in the LHS of an assignment
struct LookupLhsIdentifier : public slang::ast::ASTVisitor<LookupLhsIdentifier, true, true> {
    explicit LookupLhsIdentifier(const std::string_view& name) : name(name) {}

    void handle(const slang::ast::AssignmentExpression& expression) {
        _found |= hasIdentifier(name, expression);
    }

    // Checks if the symbol on the LHS of the expression has the provided name
    static bool hasIdentifier(const std::string_view& name,
                              const slang::ast::AssignmentExpression& expression) {
        const slang::ast::Symbol* symbol = nullptr;
        if (slang::ast::MemberAccessExpression::isKind(expression.left().kind)) {
            auto& memberAccess = expression.left().as<slang::ast::MemberAccessExpression>();
            if (slang::ast::NamedValueExpression::isKind(memberAccess.value().kind))
                symbol = &memberAccess.value().as<slang::ast::NamedValueExpression>().symbol;
        }
        else {
            symbol = expression.left().getSymbolReference();
        }

        if (symbol && symbol->name == name) {
            return true;
        }
        return false;
    }

    // Retrieves whether the identifier has been found
    [[nodiscard]] bool found() const { return _found; }

    // Resets the state of the visitor, so it can be used again without having to create a new one
    void reset() { _found = false; }

private:
    const std::string_view name;
    bool _found = false;
};
