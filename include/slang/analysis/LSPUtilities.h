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

template<typename T>
concept IsSelectExpr = IsAnyOf<T, ast::ElementSelectExpression, ast::RangeSelectExpression,
                               ast::MemberAccessExpression, ast::HierarchicalValueExpression,
                               ast::NamedValueExpression>;

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

    /// Visits the longest static prefix expressions for all of the operands
    /// in the given expression using the provided callback function.
    template<typename TCallback>
    static void visitLSPs(const ast::Expression& expr, ast::EvalContext& evalContext,
                          TCallback&& func, const ast::Expression* initialLSP = nullptr) {
        LSPHelper<TCallback> lspHelper(evalContext, std::forward<TCallback>(func));
        lspHelper.visitor.currentLSP = initialLSP;
        expr.visit(lspHelper);
    }

    template<typename TCallback>
    static void visitComponents(const ast::Expression& longestStaticPrefix, bool includeRoot,
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

    template<typename F>
    struct LSPHelper {
        LSPVisitor<LSPHelper> visitor;
        ast::EvalContext& evalCtx;
        F&& func;

        LSPHelper(ast::EvalContext& evalCtx, F&& func) :
            visitor(*this), evalCtx(evalCtx), func(std::forward<F>(func)) {}

        ast::EvalContext& getEvalContext() const { return evalCtx; }
        bool saveLValueFlag() { return false; }

        void noteReference(const ast::ValueSymbol& symbol, const ast::Expression& lsp) {
            func(symbol, lsp);
        }

        template<typename T>
            requires(std::is_base_of_v<ast::Expression, T> && !IsSelectExpr<T>)
        void visit(const T& expr) {
            if constexpr (std::is_same_v<T, ast::Expression>) {
                // We don't have a concrete type, we need to dispatch.
                expr.visit(*this);
            }
            else {
                visitor.clear();

                if constexpr (requires { expr.visitExprs(*this); }) {
                    expr.visitExprs(*this);
                }
            }
        }

        template<typename T>
            requires(IsSelectExpr<T>)
        void visit(const T& expr) {
            visitor.handle(expr);
        }

        void visit(const ast::Pattern&) {}
        void visit(const ast::TimingControl&) {}
        void visit(const ast::Constraint&) {}
        void visit(const ast::AssertionExpr&) {}
    };
};

} // namespace slang::analysis
