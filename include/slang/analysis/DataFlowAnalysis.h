//------------------------------------------------------------------------------
//! @file DataFlowAnalysis.h
//! @brief Data flow analysis pass
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/analysis/AbstractFlowAnalysis.h"
#include "slang/analysis/AnalysisManager.h"
#include "slang/util/IntervalMap.h"
#include "slang/util/SmallMap.h"
#include "slang/util/SmallVector.h"

namespace slang::analysis {

template<typename T>
concept IsSelectExpr =
    IsAnyOf<T, ElementSelectExpression, RangeSelectExpression, MemberAccessExpression,
            HierarchicalValueExpression, NamedValueExpression>;

using SymbolBitMap = IntervalMap<uint64_t, std::monostate, 3>;
using SymbolLSPMap = IntervalMap<uint64_t, const Expression*, 5>;

/// Represents the state of a data flow analysis at a single point in a procedure.
struct SLANG_EXPORT DataFlowState {
    /// Each tracked variable has its assigned intervals stored here.
    SmallVector<SymbolBitMap, 2> assigned;

    /// Whether the control flow that arrived at this point is reachable.
    bool reachable = true;

    DataFlowState() = default;
    DataFlowState(DataFlowState&& other) = default;
    DataFlowState& operator=(DataFlowState&& other) = default;
};

/// Performs data flow analysis on a single procedure, tracking the assigned ranges
/// of nets and variables at each point in the procedure.
class SLANG_EXPORT DataFlowAnalysis : public AbstractFlowAnalysis<DataFlowAnalysis, DataFlowState> {
public:
    /// The analysis context within which the analysis is being performed.
    AnalysisContext& context;

    /// Constructs a new DataFlowAnalysis object.
    DataFlowAnalysis(AnalysisContext& context, const Symbol& symbol, bool reportDiags);

    /// Visits all of the symbols that are assigned anywhere in the procedure
    /// and aren't definitely assigned by the end of the procedure.
    template<typename F>
    void visitLatches(F&& func) const;

    /// Gets all of the statements in the procedure that have timing controls
    /// associated with them.
    std::span<const Statement* const> getTimedStatements() const { return timedStatements; }

    /// Gets all of the concurrent assertions and procedural checkers in the procedure.
    std::span<const Statement* const> getAssertionStatements() const {
        return concurrentAssertions;
    }

    /// Determines whether the given symbol is referenced anywhere in
    /// the procedure, either as an lvalue or an rvalue.
    bool isReferenced(const ValueSymbol& symbol) const {
        return symbolToSlot.contains(&symbol) || rvalues.contains(&symbol);
    }

    /// Determines whether the given subset of the symbol (via the provided
    /// longest static prefix expression) is referenced anywhere in
    /// the procedure, either as an lvalue or an rvalue.
    bool isReferenced(const ValueSymbol& symbol, const Expression& lsp) const;

    /// Visits the longest static prefix expressions for all of the operands
    /// in the given expression using the provided callback function.
    template<typename F>
    void visitLongestStaticPrefixes(const Expression& expr, F&& func) const;

    /// Gets the inferred clock for the procedure, if one exists.
    const TimingControl* inferClock(const AnalyzedProcedure* parentProcedure) const;

    /// Returns true if the procedure has any return statements.
    bool hasReturnStatements() const { return !getReturnStates().empty(); }

    /// Returns true if the current state is reachable.
    bool isReachable() const { return getState().reachable; }

    /// Returns true if the given symbol is definitely assigned at the current point.
    bool isDefinitelyAssigned(const ValueSymbol& symbol) const;

private:
    // A helper class that finds the longest static prefix of select expressions.
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

            [[maybe_unused]] auto guard = owner.saveLValueFlag();
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

            [[maybe_unused]] auto guard = owner.saveLValueFlag();
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
                [[maybe_unused]] auto guard = owner.saveLValueFlag();
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

    friend class AbstractFlowAnalysis;

    template<typename TOwner>
    friend struct LSPVisitor;

    SymbolBitMap::allocator_type bitMapAllocator;
    SymbolLSPMap::allocator_type lspMapAllocator;

    // Maps visited symbols to slots in assigned vectors.
    SmallMap<const ValueSymbol*, uint32_t, 4> symbolToSlot;

    // Tracks the assigned ranges of each variable across the entire procedure,
    // even if not all branches assign to it.
    struct LValueSymbol {
        not_null<const ValueSymbol*> symbol;
        SymbolLSPMap assigned;

        LValueSymbol(const ValueSymbol& symbol) : symbol(&symbol) {}
    };
    SmallVector<LValueSymbol> lvalues;

    // All of the nets and variables that have been read in the procedure.
    SmallMap<const ValueSymbol*, SymbolBitMap, 4> rvalues;

    // The currently active longest static prefix expression, if there is one.
    LSPVisitor<DataFlowAnalysis> lspVisitor;
    bool isLValue = false;

    // All statements that have timing controls associated with them.
    SmallVector<const Statement*> timedStatements;

    // All concurrent assertions in the procedure.
    SmallVector<const Statement*> concurrentAssertions;

    [[nodiscard]] auto saveLValueFlag() {
        auto guard = ScopeGuard([this, savedLVal = isLValue] { isLValue = savedLVal; });
        isLValue = false;
        return guard;
    }

    void noteReference(const ValueSymbol& symbol, const Expression& lsp);

    // **** AST Handlers ****

    template<typename T>
        requires(std::is_base_of_v<Expression, T> && !IsSelectExpr<T>)
    void handle(const T& expr) {
        lspVisitor.clear();
        visitExpr(expr);
    }

    template<typename T>
        requires(IsSelectExpr<T>)
    void handle(const T& expr) {
        lspVisitor.handle(expr);
    }

    template<typename T>
        requires(IsAnyOf<T, TimedStatement, WaitStatement, WaitOrderStatement, WaitForkStatement>)
    void handle(const T& stmt) {
        if constexpr (std::is_same_v<T, TimedStatement>) {
            bad |= stmt.timing.bad();
        }

        timedStatements.push_back(&stmt);
        visitStmt(stmt);
    }

    void handle(const AssignmentExpression& expr);
    void handle(const ExpressionStatement& stmt);
    void handle(const ConcurrentAssertionStatement& stmt);
    void handle(const ProceduralCheckerStatement& stmt);

    // **** State Management ****

    void joinState(DataFlowState& result, const DataFlowState& other);
    void meetState(DataFlowState& result, const DataFlowState& other);
    DataFlowState copyState(const DataFlowState& source);
    DataFlowState unreachableState() const;
    DataFlowState topState() const;

    // **** LSPHelper class ****

    // A helper for implementing the visitLongestStaticPrefixes method.
    template<typename F>
    struct LSPHelper {
        LSPVisitor<LSPHelper> visitor;
        EvalContext& evalCtx;
        F&& func;

        LSPHelper(EvalContext& evalCtx, F&& func) :
            visitor(*this), evalCtx(evalCtx), func(std::forward<F>(func)) {}

        EvalContext& getEvalContext() const { return evalCtx; }
        bool saveLValueFlag() { return false; }

        void noteReference(const ValueSymbol& symbol, const Expression& lsp) { func(symbol, lsp); }

        template<typename T>
            requires(std::is_base_of_v<Expression, T> && !IsSelectExpr<T>)
        void visit(const T& expr) {
            visitor.clear();

            if constexpr (requires { expr.visitExprs(*this); }) {
                expr.visitExprs(*this);
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

template<typename F>
void DataFlowAnalysis::visitLatches(F&& func) const {
    for (size_t index = 0; index < lvalues.size(); index++) {
        // Skip automatic variables, which can't be inferred latches.
        auto& symbolState = lvalues[index];
        auto& symbol = *symbolState.symbol;
        if (VariableSymbol::isKind(symbol.kind) &&
            symbol.as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
            continue;
        }

        auto& left = symbolState.assigned;
        SLANG_ASSERT(!left.empty());

        // Each interval in the left map is a range that needs to be fully covered
        // by our final state, otherwise that interval is not fully assigned.
        auto& currState = getState();
        if (currState.assigned.size() <= index) {
            for (auto it = left.begin(); it != left.end(); ++it)
                func(symbol, **it);
            continue;
        }

        auto& right = currState.assigned[index];
        for (auto lit = left.begin(); lit != left.end(); ++lit) {
            auto lbounds = lit.bounds();
            if (auto rit = right.find(lbounds); rit != right.end()) {
                // If this right hand side interval doesn't completely cover
                // the left hand side one then we don't need to look further.
                // The rhs intervals are unioned so there otherwise must be a
                // gap and so the lhs interval is not fully assigned.
                auto rbounds = rit.bounds();
                if (rbounds.first <= lbounds.first && rbounds.second >= lbounds.second)
                    continue;
            }
            func(symbol, **lit);
        }
    }
}

template<typename F>
void DataFlowAnalysis::visitLongestStaticPrefixes(const Expression& expr, F&& func) const {
    LSPHelper<F> lspHelper(getEvalContext(), std::forward<F>(func));
    expr.visit(lspHelper);
}

} // namespace slang::analysis
