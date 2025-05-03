//------------------------------------------------------------------------------
//! @file LSPUtilities.h
//! @brief Helpers for longest static prefix (LSP) analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/expressions/ConversionExpression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/text/FormatBuffer.h"

namespace slang::analysis {

/// A helper class that finds the longest static prefix of expressions.
template<typename TOwner>
struct LSPVisitor {
    TOwner& owner;
    const ast::Expression* currentLSP = nullptr;

    explicit LSPVisitor(TOwner& owner) : owner(owner) {}

    void clear() { currentLSP = nullptr; }

    void handle(const ast::ElementSelectExpression& expr) {
        if (expr.isConstantSelect(owner.getEvalContext())) {
            if (!currentLSP)
                currentLSP = &expr;
        }
        else {
            currentLSP = nullptr;
        }

        owner.visit(expr.value());

        [[maybe_unused]] auto guard = owner.saveLValueFlag();
        owner.visit(expr.selector());
    }

    void handle(const ast::RangeSelectExpression& expr) {
        if (expr.isConstantSelect(owner.getEvalContext())) {
            if (!currentLSP)
                currentLSP = &expr;
        }
        else {
            currentLSP = nullptr;
        }

        owner.visit(expr.value());

        [[maybe_unused]] auto guard = owner.saveLValueFlag();
        owner.visit(expr.left());
        owner.visit(expr.right());
    }

    void handle(const ast::MemberAccessExpression& expr) {
        // If this is a selection of a class or covergroup member,
        // the lsp depends only on the selected member and not on
        // the handle itself. Otherwise, the opposite is true.
        auto& valueType = expr.value().type->getCanonicalType();
        if (valueType.isClass() || valueType.isCovergroup() || valueType.isVoid()) {
            auto lsp = std::exchange(currentLSP, nullptr);
            if (!lsp)
                lsp = &expr;

            if (ast::VariableSymbol::isKind(expr.member.kind))
                owner.noteReference(expr.member.as<ast::VariableSymbol>(), *lsp);

            // Make sure the value gets visited but not as an lvalue anymore.
            [[maybe_unused]] auto guard = owner.saveLValueFlag();
            owner.visit(expr.value());
        }
        else {
            if (!currentLSP)
                currentLSP = &expr;

            owner.visit(expr.value());
        }
    }

    void handle(const ast::HierarchicalValueExpression& expr) {
        auto lsp = std::exchange(currentLSP, nullptr);
        if (!lsp)
            lsp = &expr;

        owner.noteReference(expr.symbol, *lsp);
    }

    void handle(const ast::NamedValueExpression& expr) {
        auto lsp = std::exchange(currentLSP, nullptr);
        if (!lsp)
            lsp = &expr;

        owner.noteReference(expr.symbol, *lsp);
    }
};

/// A collection of utility methods for working with LSP expressions.
class SLANG_EXPORT LSPUtilities {
public:
    static void stringifyLSP(const ast::Expression& expr, ast::EvalContext& evalContext,
                             FormatBuffer& buffer);

    template<typename TCallback>
    static void visitLSP(const ast::Expression& longestStaticPrefix, bool includeRoot,
                         TCallback&& callback) {
        using ExpressionKind = ast::ExpressionKind;

        auto expr = &longestStaticPrefix;
        do {
            switch (expr->kind) {
                case ExpressionKind::NamedValue:
                case ExpressionKind::HierarchicalValue:
                case ExpressionKind::Call:
                    if (includeRoot)
                        callback(*expr);
                    expr = nullptr;
                    break;
                case ExpressionKind::Conversion:
                    expr = &expr->as<ast::ConversionExpression>().operand();
                    break;
                case ExpressionKind::ElementSelect:
                    callback(*expr);
                    expr = &expr->as<ast::ElementSelectExpression>().value();
                    break;
                case ExpressionKind::RangeSelect:
                    callback(*expr);
                    expr = &expr->as<ast::RangeSelectExpression>().value();
                    break;
                case ExpressionKind::MemberAccess: {
                    auto& access = expr->as<ast::MemberAccessExpression>();
                    if (access.member.kind == ast::SymbolKind::Field) {
                        callback(*expr);
                        expr = &access.value();
                    }
                    else {
                        expr = nullptr;
                    }
                    break;
                }
                default:
                    SLANG_UNREACHABLE;
            }
        } while (expr);
    }

private:
    LSPUtilities() = delete;
};

} // namespace slang::analysis
