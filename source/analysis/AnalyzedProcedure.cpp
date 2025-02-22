//------------------------------------------------------------------------------
// AnalyzedProcedure.cpp
// Analysis support for procedures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AnalyzedProcedure.h"

#include "slang/analysis/DataFlowAnalysis.h"
#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

using namespace ast;

static const TimingControl* inferClock(const ProceduralBlockSymbol& procedureSymbol,
                                       const DataFlowAnalysis& dfa) {
    // Final blocks don't infer clocks.
    if (procedureSymbol.procedureKind == ProceduralBlockKind::Final)
        return nullptr;

    // 16.14.6: There must be no blocking timing controls and exactly one event control.
    const TimingControl* eventControl = nullptr;
    for (auto stmt : dfa.getTimedStatements()) {
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
            dfa.visitLongestStaticPrefixes(timing.expr,
                                           [&](const ValueSymbol& symbol, const Expression& lsp) {
                                               if (dfa.isReferenced(symbol, lsp))
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
                if (symbol.getType().isEvent() && !dfa.isReferenced(symbol)) {
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

AnalyzedProcedure::AnalyzedProcedure(AnalysisContext& context, const Symbol& analyzedSymbol) :
    analyzedSymbol(&analyzedSymbol) {

    DataFlowAnalysis dfa(context, analyzedSymbol);
    switch (analyzedSymbol.kind) {
        case SymbolKind::ProceduralBlock:
            dfa.run(analyzedSymbol.as<ProceduralBlockSymbol>().getBody());
            break;
        case SymbolKind::Subroutine:
            dfa.run(analyzedSymbol.as<SubroutineSymbol>().getBody());
            break;
        default:
            SLANG_UNREACHABLE;
    }

    if (dfa.bad)
        return;

    if (analyzedSymbol.kind == SymbolKind::ProceduralBlock) {
        auto& procedure = analyzedSymbol.as<ProceduralBlockSymbol>();
        if (procedure.procedureKind == ProceduralBlockKind::AlwaysComb) {
            SmallVector<std::pair<const Symbol*, const Expression*>> partiallyAssigned;
            dfa.getPartiallyAssignedSymbols(partiallyAssigned);

            for (auto [symbol, expr] : partiallyAssigned) {
                // Skip automatic variables, which can't be inferred latches.
                if (VariableSymbol::isKind(symbol->kind) &&
                    symbol->as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
                    continue;
                }
                context.addDiag(procedure, diag::InferredLatch, expr->sourceRange) << symbol->name;
            }
        }

        if (!dfa.getConcurrentAssertions().empty())
            inferredClock = inferClock(procedure, dfa);
    }
}

} // namespace slang::analysis
