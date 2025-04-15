//------------------------------------------------------------------------------
// DataFlowAnalysis.cpp
// Data flow analysis pass
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/DataFlowAnalysis.h"

#include "slang/analysis/ClockInference.h"

namespace slang::analysis {

DataFlowAnalysis::DataFlowAnalysis(AnalysisContext& context, const Symbol& symbol,
                                   bool reportDiags) :
    AbstractFlowAnalysis(symbol, context.manager->getOptions(),
                         reportDiags ? &context.diagnostics : nullptr),
    context(context), bitMapAllocator(context.alloc), lspMapAllocator(context.alloc),
    lspVisitor(*this) {
}

bool DataFlowAnalysis::isReferenced(const ValueSymbol& symbol, const Expression& lsp) const {
    auto bounds = ValueDriver::getBounds(lsp, getEvalContext(), symbol.getType());
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

bool DataFlowAnalysis::isDefinitelyAssigned(const ValueSymbol& symbol) const {
    auto it = symbolToSlot.find(&symbol);
    if (it == symbolToSlot.end())
        return false;

    auto& assigned = getState().assigned;
    return it->second < assigned.size() && !assigned[it->second].empty();
}

void DataFlowAnalysis::noteReference(const ValueSymbol& symbol, const Expression& lsp) {
    // This feels icky but we don't count a symbol as being referenced in the procedure
    // if it's only used inside an unreachable flow path. The alternative would just
    // frustrate users, but the reason it's icky is because whether a path is reachable
    // is based on whatever level of heuristics we're willing to implement rather than
    // some well defined set of rules in the LRM.
    auto& currState = getState();
    if (!currState.reachable)
        return;

    auto bounds = ValueDriver::getBounds(lsp, getEvalContext(), symbol.getType());
    if (!bounds) {
        // This probably cannot be hit given that we early out elsewhere for
        // invalid expressions.
        return;
    }

    if (isLValue) {
        auto [it, inserted] = symbolToSlot.try_emplace(&symbol, (uint32_t)lvalues.size());
        if (inserted) {
            lvalues.emplace_back(symbol);
            SLANG_ASSERT(lvalues.size() == symbolToSlot.size());
        }

        auto index = it->second;
        if (index >= currState.assigned.size())
            currState.assigned.resize(index + 1);

        currState.assigned[index].unionWith(*bounds, {}, bitMapAllocator);

        auto& lspMap = lvalues[index].assigned;
        for (auto lspIt = lspMap.find(*bounds); lspIt != lspMap.end();) {
            // If we find an existing entry that completely contains
            // the new bounds we can just keep that one and ignore the
            // new one. Otherwise we will insert a new entry.
            auto itBounds = lspIt.bounds();
            if (itBounds.first <= bounds->first && itBounds.second >= bounds->second)
                return;

            // If the new bounds completely contain the existing entry, we can remove it.
            if (bounds->first < itBounds.first && bounds->second > itBounds.second) {
                lspMap.erase(lspIt, lspMapAllocator);
                lspIt = lspMap.find(*bounds);
            }
            else {
                ++lspIt;
            }
        }
        lspMap.insert(*bounds, &lsp, lspMapAllocator);
    }
    else {
        rvalues[&symbol].unionWith(*bounds, {}, bitMapAllocator);
    }
}

void DataFlowAnalysis::handle(const AssignmentExpression& expr) {
    // Note that this method mirrors the logic in the base class
    // handler but we need to track the LValue status of the lhs.
    SLANG_ASSERT(!isLValue);
    isLValue = true;
    visit(expr.left());
    isLValue = false;

    if (!expr.isLValueArg())
        visit(expr.right());
}

void DataFlowAnalysis::handle(const ExpressionStatement& stmt) {
    visitStmt(stmt);

    if (stmt.expr.kind == ExpressionKind::Assignment) {
        auto& assignment = stmt.expr.as<AssignmentExpression>();
        if (assignment.timingControl) {
            bad |= assignment.timingControl->bad();
            timedStatements.push_back(&stmt);
        }
    }
}

void DataFlowAnalysis::handle(const ConcurrentAssertionStatement& stmt) {
    concurrentAssertions.push_back(&stmt);
    visitStmt(stmt);
}

void DataFlowAnalysis::handle(const ProceduralCheckerStatement& stmt) {
    concurrentAssertions.push_back(&stmt);
    visitStmt(stmt);
}

void DataFlowAnalysis::joinState(DataFlowState& result, const DataFlowState& other) {
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

void DataFlowAnalysis::meetState(DataFlowState& result, const DataFlowState& other) {
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

DataFlowState DataFlowAnalysis::copyState(const DataFlowState& source) {
    DataFlowState result;
    result.reachable = source.reachable;
    result.assigned.reserve(source.assigned.size());
    for (size_t i = 0; i < source.assigned.size(); i++)
        result.assigned.emplace_back(source.assigned[i].clone(bitMapAllocator));
    return result;
}

DataFlowState DataFlowAnalysis::unreachableState() const {
    DataFlowState result;
    result.reachable = false;
    return result;
}

DataFlowState DataFlowAnalysis::topState() const {
    return {};
}

const TimingControl* DataFlowAnalysis::inferClock(const AnalyzedProcedure* parentProcedure) const {
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
            visitLongestStaticPrefixes(timing.expr,
                                       [&](const ValueSymbol& symbol, const Expression& lsp) {
                                           if (isReferenced(symbol, lsp))
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
