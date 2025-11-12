//------------------------------------------------------------------------------
// DFAResults.cpp
// Results of running data flow analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/DFAResults.h"

#include "slang/analysis/AnalysisManager.h"
#include "slang/analysis/ClockInference.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/LSPUtilities.h"

namespace slang::analysis {

using namespace ast;

DFAResults::DFAResults(AnalysisContext& context, const SmallVectorBase<SymbolBitMap>& stateRef) :
    bitMapAllocator(context.alloc), lspMapAllocator(context.alloc), stateRef(&stateRef) {
}

bool DFAResults::isReferenced(EvalContext& evalContext, const ValueSymbol& symbol,
                              const Expression& lsp) const {
    auto bounds = LSPUtilities::getBounds(lsp, evalContext, symbol.getType());
    if (!bounds)
        return isReferenced(symbol);

    {
        auto it = symbolToSlot.find(&symbol);
        if (it != symbolToSlot.end()) {
            auto& symbolState = lvalues[it->second];
            if (symbolState.assigned.find(*bounds) != symbolState.assigned.end())
                return true;
        }
    }
    {
        auto it = rvalues.find(&symbol);
        if (it != rvalues.end() && it->second.find(*bounds) != it->second.end())
            return true;
    }

    return false;
}

bool DFAResults::isDefinitelyAssigned(const ValueSymbol& symbol) const {
    auto it = symbolToSlot.find(&symbol);
    if (it == symbolToSlot.end())
        return false;

    auto& assigned = *stateRef;
    return it->second < assigned.size() && !assigned[it->second].empty();
}

void DFAResults::visitPartiallyAssigned(bool skipAutomatic, AssignedSymbolCB cb) const {
    auto& currState = *stateRef;
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
        if (currState.size() <= index) {
            for (auto it = left.begin(); it != left.end(); ++it)
                cb(symbol, **it);
            continue;
        }

        auto& right = currState[index];
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
            cb(symbol, **lit);
        }
    }
}

void DFAResults::visitDefinitelyAssigned(bool skipAutomatic, AssignedSymbolCB cb) const {
    auto& currState = *stateRef;
    for (size_t index = 0; index < currState.size(); index++) {
        auto& symbolState = lvalues[index];
        auto& symbol = *symbolState.symbol;

        if (skipAutomatic && VariableSymbol::isKind(symbol.kind) &&
            symbol.as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
            continue;
        }

        auto& imap = currState[index];
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
                    cb(symbol, **lspIt);
                }

                prevBounds = curBounds;
            }
        }
    }
}

const TimingControl* DFAResults::inferClock(AnalysisContext& context, const Symbol& rootSymbol,
                                            EvalContext& evalContext,
                                            const AnalyzedProcedure* parentProcedure) const {
    // 16.14.6: There must be no blocking timing controls and exactly one event control.
    const TimingControl* eventControl = nullptr;
    for (auto stmt : getTimedStatements()) {
        switch (stmt->kind) {
            case StatementKind::ExpressionStatement:
                // Non-blocking assignments are ignored, blocking assignments
                // prevent clock inference.
                if (stmt->as<ExpressionStatement>().expr.as<AssignmentExpression>().isBlocking())
                    return nullptr;
                break;
            case StatementKind::Timed: {
                auto& timed = stmt->as<TimedStatement>();
                switch (timed.timing.kind) {
                    case TimingControlKind::SignalEvent:
                    case TimingControlKind::EventList:
                        if (eventControl)
                            return nullptr;
                        eventControl = &timed.timing;
                        break;
                    default:
                        // These are blocking.
                        return nullptr;
                }
                break;
            }
            case StatementKind::Wait:
            case StatementKind::WaitFork:
            case StatementKind::WaitOrder:
                // These are blocking.
                return nullptr;
            default:
                SLANG_UNREACHABLE;
        }
    }

    if (!eventControl)
        return nullptr;

    // One and only one event expression within the event control of the procedure
    // satisfies both of the following conditions:
    //   1) The event expression consists solely of an event variable, solely of a
    //      clocking block identifier, or is of the form:
    //        `edge_identifier expression1 [ iff expression2 ]` and is not a proper
    //      subexpression of an event expression of this form.
    //   2) If the event expression consists solely of an event variable or clocking
    //      block identifier, it does not appear anywhere else in the body of the
    //      procedure other than as a reference to a clocking block signal, as a
    //      clocking event or within assertion statements. If the event expression is
    //      of the form `edge_identifier expression1 [ iff expression2 ]`, no term in
    //      expression1 appears anywhere else in the body of the procedure other than
    //      as a clocking event or within assertion statements.
    const TimingControl* inferredClock = nullptr;
    auto checkEvent = [&](const SignalEventControl& timing) {
        if (timing.edge != EdgeKind::None) {
            // This is a valid clock if every term in the expression is
            // unused elsewhere in the procedure.
            bool referenced = false;
            LSPUtilities::visitLSPs(timing.expr, evalContext,
                                    [&](const ValueSymbol& symbol, const Expression& lsp, bool) {
                                        if (isReferenced(evalContext, symbol, lsp))
                                            referenced = true;
                                    });
            if (!referenced) {
                if (inferredClock)
                    return false;
                inferredClock = &timing;
            }
            return true;
        }

        if (!timing.iffCondition) {
            if (ValueExpressionBase::isKind(timing.expr.kind)) {
                auto& symbol = timing.expr.as<ValueExpressionBase>().symbol;
                if (symbol.getType().isEvent() && !isReferenced(symbol)) {
                    // We found an event variable and it's not referenced elsewhere.
                    // This is a valid clock to infer; if we previously found one then
                    // there is no unique clock and we should return.
                    if (inferredClock)
                        return false;
                    inferredClock = &timing;
                }
            }
            else if (timing.expr.kind == ExpressionKind::ArbitrarySymbol) {
                auto& ase = timing.expr.as<ArbitrarySymbolExpression>();
                if (ase.symbol->kind == SymbolKind::ClockingBlock) {
                    // We found a clocking block identifier.
                    if (inferredClock)
                        return false;
                    inferredClock = &timing;
                }
            }
        }
        return true;
    };

    auto expanded = ClockInference::expand(context, rootSymbol, *eventControl, {}, parentProcedure);
    eventControl = expanded.clock;

    if (eventControl->kind == TimingControlKind::SignalEvent) {
        if (!checkEvent(eventControl->as<SignalEventControl>()))
            return nullptr;
    }
    else if (eventControl->kind == TimingControlKind::EventList) {
        for (auto ev : eventControl->as<EventListControl>().events) {
            if (!checkEvent(ev->as<SignalEventControl>()))
                return nullptr;
        }
    }

    return inferredClock;
}

} // namespace slang::analysis
