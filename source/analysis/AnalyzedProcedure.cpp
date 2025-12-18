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
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/LSPUtilities.h"
#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

using namespace ast;

AnalyzedProcedure::AnalyzedProcedure(const Symbol& analyzedSymbol,
                                     const AnalyzedProcedure* parentProcedure) :
    analyzedSymbol(&analyzedSymbol), parentProcedure(parentProcedure) {
}

AnalyzedProcedure::AnalyzedProcedure(AnalysisContext& context, const Symbol& analyzedSymbol,
                                     const AnalyzedProcedure* parentProcedure,
                                     const DFAResults& dfa) :
    analyzedSymbol(&analyzedSymbol), parentProcedure(parentProcedure) {

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
        if (analyzedSymbol.kind == SymbolKind::ProceduralBlock &&
            analyzedSymbol.as<ProceduralBlockSymbol>().procedureKind !=
                ProceduralBlockKind::Final) {
            inferredClock = dfa.inferClock(context, analyzedSymbol, evalContext, parentProcedure);
        }

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
            [&]() -> std::pair<const CallExpression*, std::vector<const Statement*>> {
            SmallSet<const SubroutineSymbol*, 2> visited;
            for (auto call : dfaCalls) {
                std::vector<const Statement*> results;
                manager.getTaskTimingControls(*call, visited, results);
                if (!results.empty())
                    return {call, results};
            }
            return {nullptr, {}};
        };

        auto& procedure = analyzedSymbol.as<ProceduralBlockSymbol>();
        const auto procKind = procedure.procedureKind;
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
                diag << SemanticFacts::getProcedureKindStr(procKind);
                diag.addNote(diag::NoteCalledHere, taskCall->sourceRange);
            }

            auto reportInferredDiag = [&](DiagCode code, const Expression& expr) {
                FormatBuffer buffer;
                LSPUtilities::stringifyLSP(expr, evalContext, buffer);
                context.addDiag(procedure, code, expr.sourceRange) << buffer.str();
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

        DriverList perSymbol;
        for (auto it = lvalue.assigned.begin(); it != lvalue.assigned.end(); ++it) {
            auto bounds = it.bounds();
            auto driver = ValueDriver::create(context.alloc, driverKind, **it, analyzedSymbol,
                                              DriverFlags::None);
            perSymbol.emplace_back(driver, bounds);
        }

        drivers.emplace_back(&symbol, std::move(perSymbol));
    }

    // Drivers from invoked functions also get added to the procedure,
    // unless we're analyzing a subroutine.
    if (analyzedSymbol.kind != SymbolKind::Subroutine) {
        SmallSet<const SubroutineSymbol*, 2> visited;
        for (auto call : dfaCalls)
            manager.getFunctionDrivers(*call, analyzedSymbol, visited, drivers);
    }
}

} // namespace slang::analysis
