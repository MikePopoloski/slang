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

namespace slang::ast {

template<typename T>
concept IsSelectExpr =
    IsAnyOf<T, ElementSelectExpression, RangeSelectExpression, MemberAccessExpression,
            HierarchicalValueExpression, NamedValueExpression>;

using DriverBitRange = std::pair<uint64_t, uint64_t>;

/// A helper class that finds the longest static prefix of expressions.
template<typename TOwner>
struct LSPVisitor {
    TOwner& owner;
    const Expression* currentLSP = nullptr;

    explicit LSPVisitor(TOwner& owner) : owner(owner) {}

    void clear() { currentLSP = nullptr; }

    void handle(const ElementSelectExpression& expr) {
        if (expr.isConstantSelect(owner.getEvalContext())) {
            if (!currentLSP)
                currentLSP = &expr;
        }
        else {
            currentLSP = nullptr;
        }

        owner.visit(expr.value());

        auto guard = owner.saveLValueFlag();
        owner.visit(expr.selector());
    }

    void handle(const RangeSelectExpression& expr) {
        if (expr.isConstantSelect(owner.getEvalContext())) {
            if (!currentLSP)
                currentLSP = &expr;
        }
        else {
            currentLSP = nullptr;
        }

        owner.visit(expr.value());

        auto guard = owner.saveLValueFlag();
        owner.visit(expr.left());
        owner.visit(expr.right());
    }

    void handle(const MemberAccessExpression& expr) {
        // If this is a selection of a class or covergroup member,
        // the lsp depends only on the selected member and not on
        // the handle itself. Otherwise, the opposite is true.
        auto& valueType = expr.value().type->getCanonicalType();
        if (valueType.isClass() || valueType.isCovergroup() || valueType.isVoid()) {
            auto lsp = std::exchange(currentLSP, nullptr);
            if (!lsp)
                lsp = &expr;

            if (VariableSymbol::isKind(expr.member.kind))
                owner.noteReference(expr.member.as<VariableSymbol>(), *lsp);

            // Make sure the value gets visited but not as an lvalue anymore.
            auto guard = owner.saveLValueFlag();
            owner.visit(expr.value());
        }
        else {
            if (!currentLSP)
                currentLSP = &expr;

            owner.visit(expr.value());
        }
    }

    void handle(const HierarchicalValueExpression& expr) {
        auto lsp = std::exchange(currentLSP, nullptr);
        if (!lsp)
            lsp = &expr;

        owner.noteReference(expr.symbol, *lsp);
    }

    void handle(const NamedValueExpression& expr) {
        auto lsp = std::exchange(currentLSP, nullptr);
        if (!lsp)
            lsp = &expr;

        owner.noteReference(expr.symbol, *lsp);
    }
};

/// A collection of utility methods for working with LSP expressions.
class SLANG_EXPORT LSPUtilities {
public:
    static void stringifyLSP(const Expression& expr, EvalContext& evalContext,
                             FormatBuffer& buffer);

    /// Computes bounds for a driver given its longest static prefix expression.
    static std::optional<DriverBitRange> getBounds(const Expression& prefixExpression,
                                                   EvalContext& evalContext, const Type& rootType);

    /// Visits the longest static prefix expressions for all of the operands
    /// in the given expression using the provided callback function.
    template<typename TCallback>
    static void visitLSPs(const Expression& expr, EvalContext& evalContext, TCallback&& func,
                          const Expression* initialLSP = nullptr) {
        LSPHelper<TCallback> lspHelper(evalContext, std::forward<TCallback>(func));
        lspHelper.visitor.currentLSP = initialLSP;
        expr.visit(lspHelper);
    }

    template<typename TCallback>
    static void visitComponents(const Expression& longestStaticPrefix, bool includeRoot,
                                TCallback&& callback) {
        using ExpressionKind = ExpressionKind;

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
                    expr = &expr->as<ConversionExpression>().operand();
                    break;
                case ExpressionKind::ElementSelect:
                    callback(*expr);
                    expr = &expr->as<ElementSelectExpression>().value();
                    break;
                case ExpressionKind::RangeSelect:
                    callback(*expr);
                    expr = &expr->as<RangeSelectExpression>().value();
                    break;
                case ExpressionKind::MemberAccess: {
                    auto& access = expr->as<MemberAccessExpression>();
                    if (access.member.kind == SymbolKind::Field) {
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
        EvalContext& evalCtx;
        F&& func;
        bool isLValue = true;

        LSPHelper(EvalContext& evalCtx, F&& func) :
            visitor(*this), evalCtx(evalCtx), func(std::forward<F>(func)) {}

        EvalContext& getEvalContext() const { return evalCtx; }

        [[nodiscard]] auto saveLValueFlag() {
            auto guard = ScopeGuard([this, savedLVal = isLValue] { isLValue = savedLVal; });
            isLValue = false;
            return guard;
        }

        void noteReference(const ValueSymbol& symbol, const Expression& lsp) {
            func(symbol, lsp, isLValue);
        }

        template<typename T>
            requires(std::is_base_of_v<Expression, T> && !IsSelectExpr<T>)
        void visit(const T& expr) {
            if constexpr (std::is_same_v<T, Expression>) {
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

        void visit(const Pattern&) {}
        void visit(const TimingControl&) {}
        void visit(const Constraint&) {}
        void visit(const AssertionExpr&) {}
    };
};

} // namespace slang::ast
