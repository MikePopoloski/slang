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
#include "slang/analysis/ValueDriver.h"
#include "slang/ast/LSPUtilities.h"
#include "slang/util/IntervalMap.h"
#include "slang/util/SmallMap.h"
#include "slang/util/SmallVector.h"

namespace slang::analysis {

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

    /// Gets all of the statements in the procedure that have timing controls
    /// associated with them.
    std::span<const Statement* const> getTimedStatements() const { return timedStatements; }

    /// Gets all of the concurrent assertions, procedural checkers, and assertion
    /// instance expressions in the procedure.
    std::span<std::variant<const Statement*, const Expression*> const> getAssertions() const {
        return concurrentAssertions;
    }

    /// Gets all of the subroutine calls in the procedure.
    std::span<const CallExpression* const> getCallExpressions() const { return callExpressions; }

    /// Determines whether the given symbol is referenced anywhere in
    /// the procedure, either as an lvalue or an rvalue.
    bool isReferenced(const ValueSymbol& symbol) const {
        return symbolToSlot.contains(&symbol) || rvalues.contains(&symbol);
    }

    /// Determines whether the given subset of the symbol (via the provided
    /// longest static prefix expression) is referenced anywhere in
    /// the procedure, either as an lvalue or an rvalue.
    bool isReferenced(const ValueSymbol& symbol, const Expression& lsp) const;

    /// Gets the inferred clock for the procedure, if one exists.
    const TimingControl* inferClock(const AnalyzedProcedure* parentProcedure) const;

    /// Returns true if the procedure has any return statements.
    bool hasReturnStatements() const { return !getReturnStates().empty(); }

    /// Returns true if the current state is reachable.
    bool isReachable() const { return getState().reachable; }

    /// Returns true if the given symbol is definitely assigned at the current point.
    bool isDefinitelyAssigned(const ValueSymbol& symbol) const;

    /// Visits all of the symbols that are assigned anywhere in the procedure
    /// and aren't definitely assigned by the end of the procedure.
    template<typename F>
    void visitPartiallyAssigned(bool skipAutomatic, F&& func) const;

    /// Visits all of the symbols (and LSP ranges) that are definitely assigned at
    /// the current point in the procedure.
    template<typename F>
    void visitDefinitelyAssigned(bool skipAutomatic, F&& func) const;

    // Tracks assigned ranges of symbols used as lvalues in the procedure.
    struct LValueSymbol {
        not_null<const ValueSymbol*> symbol;
        SymbolLSPMap assigned;

        LValueSymbol(const ValueSymbol& symbol) : symbol(&symbol) {}
    };

    /// Gets all of the lvalues used in the procedure.
    std::span<const LValueSymbol> getLValues() const { return lvalues; }

    /// Performs handling for a timing control contained in the procedure.
    void handleTiming(const TimingControl& timing);

private:
    friend class AbstractFlowAnalysis;

    template<typename TOwner>
    friend struct ast::LSPVisitor;

    SymbolBitMap::allocator_type bitMapAllocator;
    SymbolLSPMap::allocator_type lspMapAllocator;

    // Maps visited symbols to slots in assigned vectors.
    SmallMap<const ValueSymbol*, uint32_t, 4> symbolToSlot;

    // Tracks the assigned ranges of each variable across the entire procedure,
    // even if not all branches assign to it.
    SmallVector<LValueSymbol> lvalues;

    // All of the nets and variables that have been read in the procedure.
    SmallMap<const ValueSymbol*, SymbolBitMap, 4> rvalues;

    // The currently active longest static prefix expression, if there is one.
    LSPVisitor<DataFlowAnalysis> lspVisitor;
    bool isLValue = false;
    bool prohibitLValue = false;

    // All statements that have timing controls associated with them.
    SmallVector<const Statement*> timedStatements;

    // All concurrent assertions, checkers, and assertion instance expressions in the procedure.
    SmallVector<std::variant<const Statement*, const Expression*>> concurrentAssertions;

    // All call expressions in the procedure.
    SmallVector<const CallExpression*> callExpressions;

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
            handleTiming(stmt.timing);
        }

        timedStatements.push_back(&stmt);
        visitStmt(stmt);
    }

    void handle(const ProceduralAssignStatement& stmt) {
        // Procedural force statements don't act as drivers
        // of their lvalue target.
        if (stmt.isForce) {
            prohibitLValue = true;
            visitStmt(stmt);
            prohibitLValue = false;
        }
        else {
            visitStmt(stmt);
        }
    }

    void handle(const AssignmentExpression& expr);
    void handle(const CallExpression& expr);
    void handle(const ExpressionStatement& stmt);
    void handle(const ConcurrentAssertionStatement& stmt);
    void handle(const ProceduralCheckerStatement& stmt);
    void handle(const AssertionInstanceExpression& expr);
    void handle(const EventTriggerStatement& stmt);

    // **** State Management ****

    void joinState(DataFlowState& result, const DataFlowState& other);
    void meetState(DataFlowState& result, const DataFlowState& other);
    DataFlowState copyState(const DataFlowState& source);
    DataFlowState unreachableState() const;
    DataFlowState topState() const;
};

template<typename F>
void DataFlowAnalysis::visitPartiallyAssigned(bool skipAutomatic, F&& func) const {
    auto& currState = getState();
    for (size_t index = 0; index < lvalues.size(); index++) {
        auto& symbolState = lvalues[index];
        auto& symbol = *symbolState.symbol;

        if (skipAutomatic && VariableSymbol::isKind(symbol.kind) &&
            symbol.as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
            continue;
        }

        auto& left = symbolState.assigned;
        SLANG_ASSERT(!left.empty());

        // Each interval in the left map is a range that needs to be fully covered
        // by our final state, otherwise that interval is not fully assigned.
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
void DataFlowAnalysis::visitDefinitelyAssigned(bool skipAutomatic, F&& func) const {
    auto& currState = getState();
    for (size_t index = 0; index < currState.assigned.size(); index++) {
        auto& symbolState = lvalues[index];
        auto& symbol = *symbolState.symbol;

        if (skipAutomatic && VariableSymbol::isKind(symbol.kind) &&
            symbol.as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
            continue;
        }

        auto& imap = currState.assigned[index];
        for (auto it = imap.begin(); it != imap.end(); ++it) {
            // We know this range is definitely assigned. In order to provide an
            // example expression for the LSP we need to look up a range that
            // overlaps from the procedure-wide tracking map.
            std::optional<std::pair<uint64_t, uint64_t>> prevBounds;
            for (auto lspIt = symbolState.assigned.find(it.bounds());
                 lspIt != symbolState.assigned.end(); ++lspIt) {
                // Skip over ranges that partially overlap previously visited ranges,
                // as it's not clear that there's additional value in reporting them.
                auto curBounds = lspIt.bounds();
                if (!prevBounds || prevBounds->first > curBounds.second ||
                    prevBounds->second < curBounds.first) {
                    func(symbol, **lspIt);
                }

                prevBounds = curBounds;
            }
        }
    }
}

} // namespace slang::analysis
