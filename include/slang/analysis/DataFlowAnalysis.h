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

using AssignedBitMap = IntervalMap<uint64_t, std::monostate, 3>;

struct DataFlowState {
    // Each tracked variable has its assigned intervals stored here.
    // This should be 64 bytes per variable.
    SmallVector<AssignedBitMap, 2> assigned;

    // Whether the control flow that arrived at this point is reachable.
    bool reachable = true;

    DataFlowState() = default;
    DataFlowState(DataFlowState&& other) = default;
    DataFlowState& operator=(DataFlowState&& other) = default;
};

/// Performs data flow analysis on a single procedure, tracking the assigned ranges
/// of nets and variables at each point in the procedure.
class DataFlowAnalysis : public AbstractFlowAnalysis<DataFlowAnalysis, DataFlowState> {
public:
    /// Constructs a new DataFlowAnalysis object.
    DataFlowAnalysis(AnalysisContext& context, const Symbol& symbol) :
        AbstractFlowAnalysis(symbol), context(context), assignedBitAllocator(context.alloc) {}

    /// Gets all of the symbols that are assigned anywhere in the procedure
    /// and aren't fully assigned by the end of the procedure across all
    /// control flow paths.
    void getPartiallyAssignedSymbols(
        SmallVector<std::pair<const Symbol*, const Expression*>>& results) const {
        for (size_t index = 0; index < seenSymbols.size(); index++) {
            auto& symbolState = seenSymbols[index];
            if (state.assigned.size() <= index ||
                !isFullyAssigned(symbolState.assigned, state.assigned[index])) {
                results.push_back({symbolState.symbol, symbolState.firstLSP});
            }
        }
    }

private:
    friend class AbstractFlowAnalysis;

    AnalysisContext& context;
    AssignedBitMap::allocator_type assignedBitAllocator;

    // Maps visited symbols to slots in assigned vectors.
    SmallMap<const Symbol*, uint32_t, 4> symbolToSlot;

    // Tracks the assigned ranges of each variable across the entire procedure,
    // even if not all branches assign to it.
    struct SymbolState {
        const Symbol* symbol;
        const Expression* firstLSP;
        AssignedBitMap assigned;

        SymbolState(const Symbol* symbol, const Expression* firstLSP) :
            symbol(symbol), firstLSP(firstLSP) {}
    };
    SmallVector<SymbolState> seenSymbols;

    void handle(const AssignmentExpression& expr) {
        visitExpr(expr);

        SmallVector<std::pair<const ValueSymbol*, const Expression*>> prefixes;
        expr.left().getLongestStaticPrefixes(prefixes, evalContext);

        for (auto [symbol, prefix] : prefixes) {
            auto [it, inserted] = symbolToSlot.try_emplace(symbol, seenSymbols.size());
            if (inserted) {
                seenSymbols.emplace_back(symbol, prefix);
                SLANG_ASSERT(seenSymbols.size() == symbolToSlot.size());
            }

            auto index = it->second;
            if (index >= state.assigned.size())
                state.assigned.resize(index + 1);

            auto bounds = ValueDriver::getBounds(*prefix, evalContext, symbol->getType());
            if (bounds) {
                state.assigned[index].unionWith(*bounds, {}, assignedBitAllocator);
                seenSymbols[index].assigned.unionWith(*bounds, {}, assignedBitAllocator);
            }
        }
    }

    void joinState(DataFlowState& state, const DataFlowState& other) {
        if (state.reachable == other.reachable) {
            if (state.assigned.size() > other.assigned.size())
                state.assigned.resize(other.assigned.size());

            for (size_t i = 0; i < state.assigned.size(); i++) {
                state.assigned[i] = state.assigned[i].intersection(other.assigned[i],
                                                                   assignedBitAllocator);
            }
        }
        else if (!state.reachable) {
            state = copyState(other);
        }
    }

    void meetState(DataFlowState& state, const DataFlowState& other) {
        if (!other.reachable) {
            state.reachable = false;
            return;
        }

        // Union the assigned state across each variable.
        if (state.assigned.size() < other.assigned.size())
            state.assigned.resize(other.assigned.size());

        for (size_t i = 0; i < other.assigned.size(); i++) {
            for (auto it = other.assigned[i].begin(); it != other.assigned[i].end(); ++it)
                state.assigned[i].unionWith(it.bounds(), *it, assignedBitAllocator);
        }
    }

    DataFlowState copyState(const DataFlowState& state) {
        DataFlowState result;
        result.reachable = state.reachable;
        result.assigned.reserve(state.assigned.size());
        for (size_t i = 0; i < state.assigned.size(); i++)
            result.assigned.emplace_back(state.assigned[i].clone(assignedBitAllocator));
        return result;
    }

    DataFlowState unreachableState() const {
        DataFlowState result;
        result.reachable = false;
        return result;
    }

    DataFlowState topState() const { return {}; }

    bool isFullyAssigned(const AssignedBitMap& left, const AssignedBitMap& right) const {
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
};

} // namespace slang::analysis
