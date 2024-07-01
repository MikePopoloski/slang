//------------------------------------------------------------------------------
//! @file ASTHelperVisitors.h
//! @brief Reusable AST visitors and functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "TidyConfig.h"
#include "TidyFactory.h"
#include <filesystem>

#include "slang/ast/ASTVisitor.h"

#define NEEDS_SKIP_SYMBOL(__symbol)                            \
    if (skip(sourceManager->getFileName((__symbol).location))) \
        return;

// Function that tries to get the name of the variable in an expression
std::optional<std::string_view> getIdentifier(const slang::ast::Expression& expr);

// Function that tries to get the source location of an expression
std::optional<slang::SourceLocation> getExpressionSourceLocation(
    const slang::ast::Expression& expr);

struct TidyVisitor {
protected:
    explicit TidyVisitor(slang::Diagnostics& diagnostics) :
        sourceManager(Registry::getSourceManager()), diags(diagnostics),
        config(Registry::getConfig()) {}

    [[nodiscard]] bool skip(std::string_view path) const {
        auto file = std::filesystem::path(path).filename().string();
        auto parentPath = weakly_canonical(std::filesystem::path(path).parent_path());
        const auto& skipFiles = config.getSkipFiles();
        const auto& skipPaths = config.getSkipPaths();
        return std::find(skipFiles.begin(), skipFiles.end(), file) != skipFiles.end() ||
               std::find_if(skipPaths.begin(), skipPaths.end(), [&](auto& path) {
                   return parentPath.string().find(path) != std::string::npos;
               }) != skipPaths.end();
    }

    slang::not_null<const slang::SourceManager*> sourceManager;
    slang::Diagnostics& diags;
    const TidyConfig& config;
};

/// ASTVisitor that will collect all identifiers under a node
struct CollectIdentifiers : public slang::ast::ASTVisitor<CollectIdentifiers, false, true> {
    void handle(const slang::ast::NamedValueExpression& expression) {
        if (auto* symbol = expression.getSymbolReference(); symbol) {
            identifiers.push_back(symbol->name);
        }
    }
    std::vector<std::string_view> identifiers;
};

/// ASTVisitor that will try to find the provided name in the identifiers under a node
struct LookupIdentifier : public slang::ast::ASTVisitor<LookupIdentifier, true, true> {
    explicit LookupIdentifier(const std::string_view& name, const bool exactMatching = true) :
        name(name), exactMatching(exactMatching) {}

    void handle(const slang::ast::NamedValueExpression& expression) {
        if (hasIdentifier(name, exactMatching, expression)) {
            _found = true;
            _foundLocation = getExpressionSourceLocation(expression);
        }
    }

    // Checks if the symbol reference of the expression has the provided name
    static bool hasIdentifier(const std::string_view& name, const bool exactMatching,
                              const slang::ast::NamedValueExpression& expression) {
        auto symbol = expression.getSymbolReference();

        return symbol && exactMatching ? symbol->name == name
                                       : symbol->name.find(name) != std::string_view::npos;
    }

    // Retrieves whether the identifier has been found
    [[nodiscard]] bool found() const { return _found; }

    // Retrieves the identifier location in case it has been found
    std::optional<slang::SourceLocation> foundLocation() const { return _foundLocation; }

    // Resets the state of the visitor, so it can be used again without having to create a new one
    void reset() {
        _found = false;
        _foundLocation = {};
    }

private:
    const std::string_view name;
    const bool exactMatching;
    bool _found = false;
    std::optional<slang::SourceLocation> _foundLocation;
};

/// ASTVisitor that will collect all LHS assignment symbols under a node
struct CollectLHSSymbols : public slang::ast::ASTVisitor<CollectLHSSymbols, true, true> {
    void handle(const slang::ast::AssignmentExpression& expression) {
        if (const auto symbol = expression.left().getSymbolReference(); symbol)
            symbols.push_back(symbol);
    }

    std::vector<const slang::ast::Symbol*> symbols;
};

/// ASTVisitor that will try to find the provided name in the LHS of an assignment
struct LookupLhsIdentifier : public slang::ast::ASTVisitor<LookupLhsIdentifier, true, true> {
    explicit LookupLhsIdentifier(const std::string_view& name) : name(name) {}

    void handle(const slang::ast::AssignmentExpression& expression) {
        if (hasIdentifier(name, expression)) {
            _found = true;
            _foundLocation = getExpressionSourceLocation(expression);
        }
    }

    // Checks if the symbol on the LHS of the expression has the provided name
    static bool hasIdentifier(const std::string_view& name,
                              const slang::ast::AssignmentExpression& expression) {
        auto identifier = getIdentifier(expression.left());

        return identifier && identifier.value() == name;
    }

    // Retrieves whether the identifier has been found
    [[nodiscard]] bool found() const { return _found; }

    // Retrieves the identifier location in case it has been found
    std::optional<slang::SourceLocation> foundLocation() const { return _foundLocation; }

    // Resets the state of the visitor, so it can be used again without having to create a new one
    void reset() {
        _found = false;
        _foundLocation = {};
    }

private:
    const std::string_view name;
    bool _found = false;
    std::optional<slang::SourceLocation> _foundLocation;
};
