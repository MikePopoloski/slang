//------------------------------------------------------------------------------
// DataFlowAnalysis.cpp
// Data flow analysis pass
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/DataFlowAnalysis.h"

#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

void DataFlowAnalysis::getPartiallyAssignedSymbols(
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

bool DataFlowAnalysis::isFullyAssigned(const SymbolBitMap& left, const SymbolBitMap& right) const {
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

void DataFlowAnalysis::noteReference(const ValueExpressionBase& expr, const Expression& lsp) {
    // TODO: think harder about whether unreachable symbol references
    // still count as usages for the procedure.
    auto& currState = getState();
    if (!currState.reachable)
        return;

    auto& symbol = expr.symbol;
    auto bounds = ValueDriver::getBounds(lsp, getEvalContext(), symbol.getType());
    if (!bounds)
        return; // TODO: what cases can get us here?

    if (isLValue) {
        auto [it, inserted] = symbolToSlot.try_emplace(&symbol, (uint32_t)lvalues.size());
        if (inserted) {
            lvalues.emplace_back(&symbol, &lsp);
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

const TimingControl* DataFlowAnalysis::inferClock() const {
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

    if (eventControl->kind == TimingControlKind::SignalEvent) {
        if (!checkEvent(eventControl->as<SignalEventControl>()))
            return nullptr;
    }
    else {
        for (auto ev : eventControl->as<EventListControl>().events) {
            if (!checkEvent(ev->as<SignalEventControl>()))
                return nullptr;
        }
    }

    return inferredClock;
}

bool DataFlowAnalysis::isInferredClockCall(const Expression& expr) {
    if (expr.kind == ExpressionKind::Call) {
        auto& call = expr.as<CallExpression>();
        if (call.isSystemCall() && call.getSubroutineName() == "$inferred_clock")
            return true;
    }
    return false;
}

DataFlowAnalysis::InferredClockResult DataFlowAnalysis::expandInferredClocking(
    AnalysisContext& context, const Symbol& parentSymbol, const TimingControl& timing,
    const TimingControl* inferredClock) {

    auto& alloc = context.alloc;
    if (timing.kind == TimingControlKind::EventList) {
        SmallVector<const TimingControl*> events;
        for (auto& event : timing.as<EventListControl>().events) {
            auto result = expandInferredClocking(context, parentSymbol, *event, inferredClock);
            if (result.clock->bad())
                return result;

            events.push_back(result.clock);
        }

        return *alloc.emplace<EventListControl>(events.copy(alloc), timing.sourceRange);
    }

    if (timing.kind == TimingControlKind::SignalEvent) {
        auto& sec = timing.as<SignalEventControl>();
        if (isInferredClockCall(sec.expr)) {
            if (!inferredClock) {
                auto& diag = context.addDiag(parentSymbol, diag::NoInferredClock,
                                             sec.expr.sourceRange);
                return {*alloc.emplace<InvalidTimingControl>(&timing), &diag};
            }
            return *inferredClock;
        }
    }

    return timing;
}

} // namespace slang::analysis
