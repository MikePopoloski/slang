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
#include "slang/util/ScopeGuard.h"

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
///
/// An LSP expression is the longest static prefix of an expression that can be
/// used to identify a particular driver of a variable. For example, in the
/// expression `a.b[3].c.d[2:0]`, if all of the selects are constant, then the entire
/// expression is the LSP. If instead we had `a.b[i].c.d[2:0]`, then the LSP would be
/// `a.b[i]`.
class SLANG_EXPORT LSPUtilities {
public:
    /// Converts an LSP expression to a human-friendly string representation.
    static void stringifyLSP(const Expression& expr, EvalContext& evalContext,
                             FormatBuffer& buffer);

    /// Computes bounds for a driver given its longest static prefix expression.
    ///
    /// @note It is assumed that @a lsp is a valid LSP expression. An exception
    ///       is thrown if that is not the case.
    static std::optional<DriverBitRange> getBounds(const Expression& lsp, EvalContext& evalContext,
                                                   const Type& rootType);

    /// Visits the longest static prefix expressions for all of the operands
    /// in the given expression using the provided callback function.
    template<typename TCallback>
    static void visitLSPs(const Expression& expr, EvalContext& evalContext, TCallback&& func,
                          bool isLValue = true) {
        LSPHelper<TCallback> lspHelper(evalContext, std::forward<TCallback>(func));
        lspHelper.isLValue = isLValue;
        expr.visit(lspHelper);
    }

    /// Visits the components of the provided LSP expression, starting from the outer
    /// expressions and invoking the callback for each sub-expression in the path.
    ///
    /// @note It is assumed that @a longestStaticPrefix is a valid LSP expression.
    ///       An exception is thrown if that is not the case.
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

    using LSPCallback = function_ref<void(const ValueSymbol&, const Expression&, bool)>;

    /// Visits the longest static prefix expressions for all of the operands
    /// in the given expression using the provided callback function.
    ///
    /// Unlike @a visitLSPs, this method will expand indirect references such as
    /// modport port connections and ref port connections.
    ///
    /// @param alloc The allocator to use for any AST nodes that need to be created
    ///              to represent expanded selections.
    /// @param expr The expression to visit and potentially expand.
    /// @param evalContext An evaluation context used to evaluate constsants.
    /// @param callback The callback to invoke for each found LSP.
    /// @param isLValue Whether this expression is an lvalue or not.
    static void expandIndirectLSPs(BumpAllocator& alloc, const Expression& expr,
                                   EvalContext& evalContext, LSPCallback callback,
                                   bool isLValue = true);

    /// Clones the given LSP expression tree into a new one that has constant select
    /// values baked into the tree.
    static const Expression& cloneLSP(BumpAllocator& alloc, const Expression& expr,
                                      EvalContext& evalContext);

    /// Clones the given LSP expression tree and replaces the base of it to point to
    /// the new target symbol.
    ///
    /// It is assumed that the new target has the same type as the old one.
    static const Expression& retargetLSP(BumpAllocator& alloc, const Expression& expr,
                                         const ValueSymbol& target);

private:
    LSPUtilities() = delete;

    static void expandIndirectLSP(BumpAllocator& alloc, EvalContext& evalContext,
                                  LSPCallback callback, const ValueSymbol& symbol,
                                  const Expression& lsp, bool isLValue);

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
