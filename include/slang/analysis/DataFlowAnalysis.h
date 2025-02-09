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

using SymbolBitMap = IntervalMap<uint64_t, std::monostate, 3>;

struct SLANG_EXPORT DataFlowState {
    // Each tracked variable has its assigned intervals stored here.
    // This should be 64 bytes per variable.
    SmallVector<SymbolBitMap, 2> assigned;

    // Whether the control flow that arrived at this point is reachable.
    bool reachable = true;

    DataFlowState() = default;
    DataFlowState(DataFlowState&& other) = default;
    DataFlowState& operator=(DataFlowState&& other) = default;
};

/// Performs data flow analysis on a single procedure, tracking the assigned ranges
/// of nets and variables at each point in the procedure.
class SLANG_EXPORT DataFlowAnalysis : public AbstractFlowAnalysis<DataFlowAnalysis, DataFlowState> {
public:
    /// Constructs a new DataFlowAnalysis object.
    DataFlowAnalysis(AnalysisContext& context, const Symbol& symbol) :
        AbstractFlowAnalysis(symbol), context(context), bitMapAllocator(context.alloc) {}

    /// Gets all of the symbols that are assigned anywhere in the procedure
    /// and aren't definitely assigned by the end of the procedure.
    void getPartiallyAssignedSymbols(
        SmallVector<std::pair<const Symbol*, const Expression*>>& results) const {

        auto& currState = getState();
        for (size_t index = 0; index < lvalues.size(); index++) {
            auto& symbolState = lvalues[index];
            if (currState.assigned.size() <= index ||
                !isFullyAssigned(symbolState.assigned, currState.assigned[index])) {
                results.push_back({symbolState.symbol, symbolState.firstLSP});
            }
        }
    }

private:
    friend class AbstractFlowAnalysis;

    AnalysisContext& context;
    SymbolBitMap::allocator_type bitMapAllocator;

    // Maps visited symbols to slots in assigned vectors.
    SmallMap<const Symbol*, uint32_t, 4> symbolToSlot;

    // Tracks the assigned ranges of each variable across the entire procedure,
    // even if not all branches assign to it.
    struct LValueSymbol {
        const ValueSymbol* symbol;
        // TODO: track LSP per bit range so we can accurately report
        // which portions of a symbol are assigned and where.
        const Expression* firstLSP;
        SymbolBitMap assigned;

        LValueSymbol(const ValueSymbol* symbol, const Expression* firstLSP) :
            symbol(symbol), firstLSP(firstLSP) {}
    };
    SmallVector<LValueSymbol> lvalues;

    // All of the nets and variables that have been read in the procedure.
    SmallMap<const ValueSymbol*, SymbolBitMap, 4> rvalues;

    // The currently active longest static prefix expression, if there is one.
    const Expression* currentLSP = nullptr;
    bool isLValue = false;

    [[nodiscard]] auto saveLValueFlag() {
        auto guard = ScopeGuard([this, savedLVal = isLValue] { isLValue = savedLVal; });
        isLValue = false;
        return guard;
    }

    bool isFullyAssigned(const SymbolBitMap& left, const SymbolBitMap& right) const {
        // The left set is the union of everything we've ever assigned
        // in this procedure, so we only need to check that the right
        // set is exactly equal to the left set.
        auto lit = left.begin(), rit = right.begin();
        auto lend = left.end(), rend = right.end();
        while (lit != lend || rit != rend) {
            if (lit == lend || rit == rend)
                return false;

            if (lit.bounds() != rit.bounds())
                return false;

            ++lit;
            ++rit;
        }
        return true;
    }

    // **** AST Handlers ****

    template<typename T>
        requires(std::is_base_of_v<Expression, T>)
    void handle(const T& expr) {
        currentLSP = nullptr;
        visitExpr(expr);
    }

    void handle(const AssignmentExpression& expr) {
        // Note that this method mirrors the logic in the base class
        // handler but we need to track the LValue status of the lhs.
        SLANG_ASSERT(!isLValue);
        SLANG_ASSERT(!currentLSP);
        isLValue = true;
        visit(expr.left());
        isLValue = false;

        if (!expr.isLValueArg()) {
            if (expr.isCompound()) {
                auto& binExpr = expr.right().as<BinaryExpression>();
                SLANG_ASSERT(binExpr.left().kind == ExpressionKind::LValueReference);
                visit(binExpr.right());
            }
            else {
                visit(expr.right());
            }
        }
    }

    void handle(const ElementSelectExpression& expr) {
        if (expr.isConstantSelect(getEvalContext())) {
            if (!currentLSP)
                currentLSP = &expr;
        }
        else {
            currentLSP = nullptr;
        }

        visit(expr.value());

        auto guard = saveLValueFlag();
        visit(expr.selector());
    }

    void handle(const RangeSelectExpression& expr) {
        if (expr.isConstantSelect(getEvalContext())) {
            if (!currentLSP)
                currentLSP = &expr;
        }
        else {
            currentLSP = nullptr;
        }

        visit(expr.value());

        auto guard = saveLValueFlag();
        visit(expr.left());
        visit(expr.right());
    }

    void handle(const MemberAccessExpression& expr) {
        if (!currentLSP)
            currentLSP = &expr;

        visit(expr.value());
    }

    void handle(const HierarchicalValueExpression& expr) { recordSymbol(expr); }
    void handle(const NamedValueExpression& expr) { recordSymbol(expr); }

    void recordSymbol(const ValueExpressionBase& expr) {
        auto lsp = std::exchange(currentLSP, nullptr);
        if (!lsp)
            lsp = &expr;

        // TODO: think harder about whether unreachable symbol references
        // still count as usages for the procedure.
        auto& currState = getState();
        if (!currState.reachable)
            return;

        auto& symbol = expr.symbol;
        auto bounds = ValueDriver::getBounds(*lsp, getEvalContext(), symbol.getType());
        if (!bounds)
            return; // TODO: what cases can get us here?

        if (isLValue) {
            auto [it, inserted] = symbolToSlot.try_emplace(&symbol, (uint32_t)lvalues.size());
            if (inserted) {
                lvalues.emplace_back(&symbol, &expr);
                SLANG_ASSERT(lvalues.size() == symbolToSlot.size());
            }

            auto index = it->second;
            if (index >= currState.assigned.size())
                currState.assigned.resize(index + 1);

            currState.assigned[index].unionWith(*bounds, {}, bitMapAllocator);
            lvalues[index].assigned.unionWith(*bounds, {}, bitMapAllocator);
        }
        else {
            rvalues[&expr.symbol].unionWith(*bounds, {}, bitMapAllocator);
        }
    }

    // **** State Management ****

    void joinState(DataFlowState& result, const DataFlowState& other) {
        if (result.reachable == other.reachable) {
            if (result.assigned.size() > other.assigned.size())
                result.assigned.resize(other.assigned.size());

            for (size_t i = 0; i < result.assigned.size(); i++) {
                result.assigned[i] = result.assigned[i].intersection(other.assigned[i],
                                                                     bitMapAllocator);
            }
        }
        else if (!result.reachable) {
            result = copyState(other);
        }
    }

    void meetState(DataFlowState& result, const DataFlowState& other) {
        if (!other.reachable) {
            result.reachable = false;
            return;
        }

        // Union the assigned state across each variable.
        if (result.assigned.size() < other.assigned.size())
            result.assigned.resize(other.assigned.size());

        for (size_t i = 0; i < other.assigned.size(); i++) {
            for (auto it = other.assigned[i].begin(); it != other.assigned[i].end(); ++it)
                result.assigned[i].unionWith(it.bounds(), *it, bitMapAllocator);
        }
    }

    DataFlowState copyState(const DataFlowState& source) {
        DataFlowState result;
        result.reachable = source.reachable;
        result.assigned.reserve(source.assigned.size());
        for (size_t i = 0; i < source.assigned.size(); i++)
            result.assigned.emplace_back(source.assigned[i].clone(bitMapAllocator));
        return result;
    }

    DataFlowState unreachableState() const {
        DataFlowState result;
        result.reachable = false;
        return result;
    }

    DataFlowState topState() const { return {}; }
};

} // namespace slang::analysis
