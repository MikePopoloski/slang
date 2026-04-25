//------------------------------------------------------------------------------
// AnalyzedProcedure.cpp
// Analysis support for procedures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AnalyzedProcedure.h"

#include "slang/analysis/AnalysisManager.h"
#include "slang/analysis/ClockInference.h"
#include "slang/analysis/DFAResults.h"
#include "slang/analysis/ValueDriver.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/ValuePath.h"
#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

using namespace ast;

AnalyzedProcedure::AnalyzedProcedure(const Symbol& analyzedSymbol,
                                     const AnalyzedProcedure* parentProcedure) :
    analyzedSymbol(&analyzedSymbol), parentProcedure(parentProcedure) {
}

AnalyzedProcedure::AnalyzedProcedure(AnalysisContext& context, const Symbol& analyzedSymbol,
                                     const AnalyzedProcedure* parentProcedure, DFAResults& dfa) :
    analyzedSymbol(&analyzedSymbol), parentProcedure(parentProcedure) {

    std::optional<ProceduralBlockKind> procKind;
    if (auto proc = analyzedSymbol.as_if<ProceduralBlockSymbol>())
        procKind = proc->procedureKind;

    auto dfaCalls = dfa.getCallExpressions();
    callExpressions.reserve(dfaCalls.size());

    bool hasSampledValueCalls = false;
    for (auto call : dfaCalls) {
        callExpressions.push_back(call);
        if (ClockInference::isSampledValueFuncCall(*call))
            hasSampledValueCalls = true;
    }

    // Store timing control statements from data flow analysis
    auto dfaTimedStatements = dfa.getTimedStatements();
    timingControls.insert(timingControls.end(), dfaTimedStatements.begin(),
                          dfaTimedStatements.end());

    EvalContext evalContext(analyzedSymbol);

    auto& manager = *context.manager;
    if (parentProcedure || !dfa.getAssertions().empty() || hasSampledValueCalls) {
        // All flavors of always and initial blocks can infer a clock.
        if (procKind.has_value() && *procKind != ProceduralBlockKind::Final)
            inferredClock = dfa.inferClock(context, analyzedSymbol, evalContext, parentProcedure);

        // If no procedural inferred clock, check the scope for a default clocking block.
        if (!inferredClock) {
            auto scope = analyzedSymbol.getParentScope();
            SLANG_ASSERT(scope);

            if (auto defaultClocking = scope->getCompilation().getDefaultClocking(*scope))
                inferredClock = &defaultClocking->as<ClockingBlockSymbol>().getEvent();
        }

        if (inferredClock && inferredClock->bad())
            return;

        for (auto& var : dfa.getAssertions()) {
            if (auto stmtPtr = std::get_if<const Statement*>(&var)) {
                auto& stmt = **stmtPtr;
                if (stmt.kind == StatementKind::ProceduralChecker) {
                    for (auto inst : stmt.as<ProceduralCheckerStatement>().instances)
                        manager.analyzeCheckerInstance(inst->as<CheckerInstanceSymbol>(), *this);
                }
                else {
                    manager.analyzeAssertion(*this, stmt.as<ConcurrentAssertionStatement>());
                }
            }
            else {
                auto& expr = *std::get<const Expression*>(var);
                manager.analyzeAssertion(*this, expr.as<AssertionInstanceExpression>());
            }
        }

        // If we have no inferred clock then all sampled value system calls must provide
        // a clocking argument explicitly.
        if (!inferredClock && hasSampledValueCalls) {
            for (auto call : callExpressions) {
                if (ClockInference::isSampledValueFuncCall(*call))
                    ClockInference::checkSampledValueFuncs(context, analyzedSymbol, *call);
            }
        }
    }

    if (analyzedSymbol.kind == SymbolKind::ProceduralBlock) {
        auto getTaskTimingControls =
            [&]() -> std::pair<const CallExpression*, SmallVector<const Statement*>> {
            SmallSet<const SubroutineSymbol*, 2> visited;
            for (auto call : dfaCalls) {
                SmallVector<const Statement*> results;
                manager.getTaskTimingControls(*call, visited, results);
                if (!results.empty())
                    return {call, results};
            }
            return {nullptr, {}};
        };

        auto& procedure = analyzedSymbol.as<ProceduralBlockSymbol>();
        if (procKind == ProceduralBlockKind::Always) {
            // Generic always procedures must have timing controls
            if (!procedure.isFromAssertion && timingControls.empty() &&
                getTaskTimingControls().second.empty()) {
                context.addDiag(procedure, diag::AlwaysWithoutTimingControl, procedure.location);
            }
        }
        else if (procKind != ProceduralBlockKind::Initial) {
            // Called tasks cannot have any timing controls.
            auto [taskCall, timingStmts] = getTaskTimingControls();
            if (taskCall) {
                auto& diag = context.addDiag(procedure, diag::BlockingDelayInTask,
                                             timingStmts.front()->sourceRange);
                diag << taskCall->getSubroutineName();
                diag << SemanticFacts::getProcedureKindStr(*procKind);
                diag.addNote(diag::NoteCalledHere, taskCall->sourceRange);
            }

            auto reportInferredDiag = [&](DiagCode code, const Expression& expr) {
                ValuePath path(expr, evalContext);
                context.addDiag(procedure, code, expr.sourceRange) << path.toString(evalContext);
            };

            if (procKind == ProceduralBlockKind::AlwaysComb) {
                // Check for partially assigned variables, which infer latches.
                dfa.visitPartiallyAssigned(/* skipAutomatic */ true,
                                           [&](const Symbol&, const Expression& expr) {
                                               reportInferredDiag(diag::InferredLatch, expr);
                                           });
            }
            else if (procKind == ProceduralBlockKind::AlwaysLatch) {
                // Check for definitely assigned variables, which infer comb logic.
                dfa.visitDefinitelyAssigned(/* skipAutomatic */ true,
                                            [&](const Symbol&, const Expression& expr) {
                                                reportInferredDiag(diag::InferredComb, expr);
                                            });
            }
        }
    }
    else if (analyzedSymbol.kind == SymbolKind::Subroutine) {
        // Diagnose missing return statements and/or incomplete
        // assignments to the return value var.
        auto& subroutine = analyzedSymbol.as<SubroutineSymbol>();
        if (dfa.endIsReachable && subroutine.subroutineKind == SubroutineKind::Function &&
            !subroutine.getReturnType().isVoid() && !subroutine.name.empty() &&
            subroutine.returnValVar) {

            // Control falls off the end of a non-void function but that is
            // fine if the return value var is definitely assigned here.
            if (!dfa.isDefinitelyAssigned(*subroutine.returnValVar)) {
                if (dfa.hasReturnStatements || dfa.isReferenced(*subroutine.returnValVar)) {
                    context.addDiag(subroutine, diag::IncompleteReturn, subroutine.location)
                        << subroutine.name;
                }
                else {
                    context.addDiag(subroutine, diag::MissingReturn, subroutine.location)
                        << subroutine.name;
                }
            }
        }
    }

    DriverKind driverKind = DriverKind::Procedural;
    if (analyzedSymbol.kind == SymbolKind::ContinuousAssign)
        driverKind = DriverKind::Continuous;

    // Build a list of drivers for all lvalues.
    auto lvalues = dfa.getLValues();
    drivers.reserve(lvalues.size());
    for (auto& lvalue : lvalues) {
        // Skip over automatic variables.
        auto& symbol = *lvalue.symbol;
        if (VariableSymbol::isKind(symbol.kind)) {
            if (symbol.as<VariableSymbol>().lifetime == VariableLifetime::Automatic)
                continue;
        }

        for (auto it = lvalue.assigned.begin(); it != lvalue.assigned.end(); ++it) {
            ValuePath path(**it, evalContext);
            auto driver = ValueDriver::create(context.alloc, driverKind, path, analyzedSymbol,
                                              DriverFlags::None);
            drivers.push_back(driver);
        }
    }

    // Drivers from invoked functions also get added to the procedure,
    // unless we're analyzing a subroutine. For procedures with implicit
    // sensitivity (always_comb, always_latch, and optionally continuous assign),
    // reads from called functions are also inlined in the same traversal.
    //
    // For continuous assignments the inlining is controlled by
    // AnalysisFlags::InlineContAssignFunctionReads because the LRM does not
    // specify the behavior; different simulators choose differently.
    const auto funcDriversStart = drivers.size();
    if (analyzedSymbol.kind != SymbolKind::Subroutine) {
        const bool needsReads = (analyzedSymbol.kind == SymbolKind::ContinuousAssign &&
                                 manager.hasFlag(AnalysisFlags::InlineContAssignFunctionReads)) ||
                                procKind == ProceduralBlockKind::AlwaysComb ||
                                procKind == ProceduralBlockKind::AlwaysLatch;

        // The visit predicate returns false if getFunctionValUses should not
        // visit a given subroutine, due to having already seen it.
        SmallSet<const SubroutineSymbol*, 2> visited;
        auto visitPred = [&](const SubroutineSymbol& sub) { return visited.insert(&sub).second; };

        for (auto call : dfaCalls) {
            manager.getFunctionValUses(*call, analyzedSymbol, visitPred, drivers,
                                       needsReads ? &readSet : nullptr);
        }
    }

    // Collect all rvalue read ranges.
    for (auto& [sym, bitMap] : dfa.getRValues()) {
        for (auto it = bitMap.begin(); it != bitMap.end(); ++it)
            readSet.push_back({sym, it.bounds()});
    }

    // Collect read sets for each @* region.
    for (auto& [stmt, symMap] : dfa.getImplicitEventRValues()) {
        ImplicitEventReadSet eventReads{stmt, {}};
        for (auto& [sym, bitMap] : symMap) {
            for (auto it = bitMap.begin(); it != bitMap.end(); ++it)
                eventReads.reads.push_back({sym, it.bounds()});
        }
        implicitEventReadSets.push_back(std::move(eventReads));
    }

    buildSensitivityList(context, dfa, evalContext,
                         {drivers.data() + funcDriversStart, drivers.size() - funcDriversStart});
}

void AnalyzedProcedure::buildSensitivityList(AnalysisContext& context, DFAResults& dfa,
                                             EvalContext& evalContext,
                                             std::span<const ValueDriver* const> funcDrivers) {
    // Returns true if a symbol is declared within the procedure and
    // should therefore be excluded from the sensitivity list.
    auto isLocal = [&](const ValueSymbol& sym) {
        if (auto var = sym.as_if<VariableSymbol>();
            var && var->lifetime == VariableLifetime::Automatic) {
            return true;
        }

        auto scope = sym.getParentScope();
        const StatementBlockSymbol* rootBlock = nullptr;
        while (scope && scope->asSymbol().kind == SymbolKind::StatementBlock) {
            rootBlock = &scope->asSymbol().as<StatementBlockSymbol>();
            scope = rootBlock->getParentScope();
        }

        // ProceduralBlockSymbol is not a Scope, so its statement blocks are added
        // to the enclosing parent scope rather than the procedural block itself.
        // Check if the root statement block belongs to this procedure.
        if (rootBlock && analyzedSymbol->kind == SymbolKind::ProceduralBlock) {
            for (auto b : analyzedSymbol->as<ProceduralBlockSymbol>().getBlocks()) {
                if (b == rootBlock)
                    return true;
            }
        }
        return false;
    };

    // Adds a read set to the sensitivity list. Local variables are excluded.
    // If forceFullRange is set, variables will assume to be fully read,
    // rather than relying on the provided bit ranges.
    auto addReads = [&](std::span<const ReadRange> reads, bool forceFullRange) {
        if (forceFullRange) {
            SmallSet<const ValueSymbol*, 4> seen;
            for (auto& rr : reads) {
                if (!isLocal(*rr.symbol) && seen.insert(rr.symbol).second) {
                    auto w = rr.symbol->getType().getSelectableWidth();
                    sensitivityList.reads.push_back({rr.symbol, {0, w > 0 ? w - 1 : 0}});
                }
            }
        }
        else {
            for (auto& rr : reads) {
                if (!isLocal(*rr.symbol))
                    sensitivityList.reads.push_back(rr);
            }
        }
    };

    auto& manager = *context.manager;
    if (analyzedSymbol->kind == SymbolKind::ContinuousAssign) {
        sensitivityList.kind = SensitivityList::Kind::Implicit;
        addReads(readSet, !manager.hasFlag(AnalysisFlags::ContAssignUsesLSPs));
        return;
    }

    if (analyzedSymbol->kind != SymbolKind::ProceduralBlock)
        return;

    auto& proc = analyzedSymbol->as<ProceduralBlockSymbol>();
    const auto procKind = proc.procedureKind;
    if (procKind == ProceduralBlockKind::AlwaysComb ||
        procKind == ProceduralBlockKind::AlwaysLatch) {
        // Build a map of bit ranges driven by called functions so that
        // function-driven bits can be excluded from the sensitivity list
        // just like locally-driven bits. dfa.getLValue() only tracks
        // lvalues driven directly in the procedure body.
        //
        // It's a little inefficient to be rebuilding this map again
        // after we linearized it, but function calls in always_**
        // blocks should be rare anyway.
        SmallMap<const ValueSymbol*, SymbolBitMap, 2> funcDrivenMap;
        for (auto driver : funcDrivers) {
            auto& map = funcDrivenMap[&driver->getSymbol()];
            map.unionWith(driver->getBounds(), {}, dfa.getBitMapAllocator());
        }

        // Merge in the local DFA ranges for each symbol that also has
        // function drivers, so funcDrivenMap provides the full picture.
        for (auto& [sym, bitMap] : funcDrivenMap) {
            if (auto lvalue = dfa.getLValue(*sym)) {
                for (auto oit = lvalue->assigned.begin(); oit.valid(); ++oit)
                    bitMap.unionWith(oit.bounds(), {}, dfa.getBitMapAllocator());
            }
        }

        // Emit only the bits in rr.bitRange not covered by drivenMap.
        auto addReadGaps = [&](auto& drivenMap, const ReadRange& rr) {
            auto [rlo, rhi] = rr.bitRange;
            uint64_t cur = rlo;
            for (auto oit = drivenMap.find(rlo, rhi); oit.valid(); ++oit) {
                auto [dlo, dhi] = oit.bounds();
                uint64_t effectiveDlo = std::max(dlo, rlo);
                uint64_t effectiveDhi = std::min(dhi, rhi);
                if (effectiveDlo > cur)
                    sensitivityList.reads.push_back({rr.symbol, {cur, effectiveDlo - 1}});
                if (effectiveDhi + 1 > cur)
                    cur = effectiveDhi + 1;
                if (cur > rhi)
                    break;
            }
            if (cur <= rhi)
                sensitivityList.reads.push_back({rr.symbol, {cur, rhi}});
        };

        for (auto& rr : readSet) {
            if (isLocal(*rr.symbol))
                continue;

            // If this symbol has function-derived drivers, use the combined
            // map (which already incorporates the local DFA ranges).
            if (auto funcIt = funcDrivenMap.find(rr.symbol); funcIt != funcDrivenMap.end()) {
                addReadGaps(funcIt->second, rr);
                continue;
            }

            auto lvalue = dfa.getLValue(*rr.symbol);
            if (!lvalue) {
                // Symbol is not driven at all; include the full read range.
                sensitivityList.reads.push_back(rr);
                continue;
            }

            addReadGaps(lvalue->assigned, rr);
        }

        sensitivityList.kind = SensitivityList::Kind::Implicit;
        return;
    }

    if (procKind == ProceduralBlockKind::Initial || procKind == ProceduralBlockKind::Final ||
        timingControls.empty()) {
        return;
    }

    // For always and always_ff: find the first event-based timing control.
    // It should always be the first statement, or for always blocks we'll
    // allow it to be the first statement inside a begin/end block.
    auto stmt = &proc.getBody();
    if (stmt->kind == StatementKind::Block) {
        stmt = &stmt->as<BlockStatement>().body;
        if (stmt->kind == StatementKind::List) {
            auto& list = stmt->as<StatementList>().list;
            if (!list.empty())
                stmt = list[0];
        }
    }

    if (stmt->kind != StatementKind::Timed || implicitEventReadSets.size() > 1) {
        sensitivityList.kind = SensitivityList::Kind::Dynamic;
        return;
    }

    auto& timing = stmt->as<TimedStatement>().timing;
    if (timing.kind == TimingControlKind::ImplicitEvent) {
        if (implicitEventReadSets.empty() || implicitEventReadSets[0].statement != stmt) {
            // It's possible for this implicit event to not be sensitive to anything,
            // if its statement is empty / doesn't read any rvalues.
            sensitivityList.kind = SensitivityList::Kind::None;
        }
        else {
            // @* sensitivity: derive reads from the matching implicit event region.
            sensitivityList.kind = SensitivityList::Kind::Implicit;
            addReads(implicitEventReadSets[0].reads,
                     !manager.hasFlag(AnalysisFlags::AlwaysStarUsesLSPs));
        }
        return;
    }

    if (timing.kind == TimingControlKind::SignalEvent ||
        timing.kind == TimingControlKind::EventList) {
        // The timing explicitly lists the sensitivities.
        sensitivityList.kind = SensitivityList::Kind::Explicit;
        sensitivityList.timingControl = &timing;

        SmallMap<const ValueSymbol*, SymbolBitMap, 2> signals;
        auto handleEvent = [&](const SignalEventControl& sec) {
            ValuePath::visitPaths(sec.expr, evalContext, [&](const ValuePath& path) {
                if (path.lsp) {
                    signals[path.rootSymbol()].unionWith(path.lspBounds, {},
                                                         dfa.getBitMapAllocator());
                }
            });
        };

        if (timing.kind == TimingControlKind::SignalEvent) {
            handleEvent(timing.as<SignalEventControl>());
        }
        else {
            for (auto ev : timing.as<EventListControl>().events)
                handleEvent(ev->as<SignalEventControl>());
        }

        for (auto& [sym, bitMap] : signals) {
            for (auto it = bitMap.begin(); it != bitMap.end(); ++it)
                sensitivityList.reads.push_back({sym, it.bounds()});
        }
        return;
    }

    // Otherwise we have something complicated.
    sensitivityList.kind = SensitivityList::Kind::Dynamic;
}

size_t AnalyzedProcedure::getMemoryUsage() const {
    size_t size = sizeof(AnalyzedProcedure);
    size += sizeof(void*) * drivers.capacity();
    size += sizeof(void*) * callExpressions.capacity();
    size += sizeof(void*) * timingControls.capacity();
    size += sizeof(ReadRange) * readSet.capacity();
    size += sizeof(ReadRange) * sensitivityList.reads.capacity();
    size += sizeof(ImplicitEventReadSet) * implicitEventReadSets.capacity();
    for (auto& set : implicitEventReadSets)
        size += sizeof(ReadRange) * set.reads.capacity();
    return size;
}

} // namespace slang::analysis
