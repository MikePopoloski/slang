//------------------------------------------------------------------------------
// AnalyzedProcedure.cpp
// Analysis support for procedures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AnalyzedProcedure.h"

#include "slang/analysis/ClockInference.h"
#include "slang/analysis/DataFlowAnalysis.h"
#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

using namespace ast;

AnalyzedProcedure::AnalyzedProcedure(AnalysisContext& context, const Symbol& analyzedSymbol,
                                     const AnalyzedProcedure* parentProcedure) :
    analyzedSymbol(&analyzedSymbol), parentProcedure(parentProcedure) {

    DriverKind driverKind = DriverKind::Procedural;
    DataFlowAnalysis dfa(context, analyzedSymbol, true);
    switch (analyzedSymbol.kind) {
        case SymbolKind::ProceduralBlock:
            dfa.run(analyzedSymbol.as<ProceduralBlockSymbol>().getBody());
            break;
        case SymbolKind::Subroutine:
            dfa.run(analyzedSymbol.as<SubroutineSymbol>().getBody());
            break;
        case SymbolKind::ContinuousAssign: {
            auto& assign = analyzedSymbol.as<ContinuousAssignSymbol>();
            if (auto delay = assign.getDelay())
                dfa.handleTiming(*delay);

            dfa.run(assign.getAssignment());
            driverKind = DriverKind::Continuous;
            break;
        }
        default:
            SLANG_UNREACHABLE;
    }

    if (dfa.bad)
        return;

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

    if (parentProcedure || !dfa.getAssertions().empty() || hasSampledValueCalls) {
        // All flavors of always and initial blocks can infer a clock.
        if (analyzedSymbol.kind == SymbolKind::ProceduralBlock &&
            analyzedSymbol.as<ProceduralBlockSymbol>().procedureKind !=
                ProceduralBlockKind::Final) {
            inferredClock = dfa.inferClock(parentProcedure);
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

        auto dfaAssertions = dfa.getAssertions();
        assertions.reserve(dfaAssertions.size());
        for (auto& var : dfaAssertions) {
            if (auto stmtPtr = std::get_if<const Statement*>(&var)) {
                auto& stmt = **stmtPtr;
                if (stmt.kind == StatementKind::ProceduralChecker) {
                    for (auto inst : stmt.as<ProceduralCheckerStatement>().instances)
                        assertions.emplace_back(context, inferredClock, *this, stmt, inst);
                }
                else {
                    assertions.emplace_back(context, inferredClock, *this, stmt, nullptr);
                }
            }
            else {
                auto& expr = *std::get<const Expression*>(var);
                assertions.emplace_back(context, inferredClock, this, analyzedSymbol, expr);
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
        auto& procedure = analyzedSymbol.as<ProceduralBlockSymbol>();

        if (procedure.procedureKind == ProceduralBlockKind::AlwaysComb) {
            dfa.visitPartiallyAssigned(/* skipAutomatic */ true, [&](const Symbol&,
                                                                     const Expression& expr) {
                FormatBuffer buffer;
                LSPUtilities::stringifyLSP(expr, dfa.getEvalContext(), buffer);

                context.addDiag(procedure, diag::InferredLatch, expr.sourceRange) << buffer.str();
            });
        }
        else if (procedure.procedureKind == ProceduralBlockKind::AlwaysLatch) {
            dfa.visitDefinitelyAssigned(/* skipAutomatic */ true, [&](const Symbol&,
                                                                      const Expression& expr) {
                FormatBuffer buffer;
                LSPUtilities::stringifyLSP(expr, dfa.getEvalContext(), buffer);

                context.addDiag(procedure, diag::InferredComb, expr.sourceRange) << buffer.str();
            });
        }
        else if (procedure.procedureKind == ProceduralBlockKind::Always) {
            // Generic always procedures must have timing controls
            if (!procedure.isFromAssertion && timingControls.empty()) {
                // Check if any called subroutines have timing controls
                bool hasTimingInSubroutines = false;
                SmallSet<const SubroutineSymbol*, 2> taskVisited;
                std::vector<const ast::Statement*> taskTimingControls;
                for (auto call : dfaCalls) {
                    context.manager->getTaskTimingControls(*call, taskVisited, taskTimingControls);
                    if (!taskTimingControls.empty()) {
                        hasTimingInSubroutines = true;
                        break;
                    }
                }

                if (!hasTimingInSubroutines) {
                    context.addDiag(procedure, diag::AlwaysWithoutTimingControl,
                                    procedure.location);
                }
            }
        }
    }
    else if (analyzedSymbol.kind == SymbolKind::Subroutine) {
        // Diagnose missing return statements and/or incomplete
        // assignments to the return value var.
        auto& subroutine = analyzedSymbol.as<SubroutineSymbol>();
        if (dfa.isReachable() && subroutine.subroutineKind == SubroutineKind::Function &&
            !subroutine.getReturnType().isVoid() && !subroutine.name.empty() &&
            subroutine.returnValVar) {

            // Control falls off the end of a non-void function but that is
            // fine if the return value var is definitely assigned here.
            if (!dfa.isDefinitelyAssigned(*subroutine.returnValVar)) {
                if (dfa.hasReturnStatements() || dfa.isReferenced(*subroutine.returnValVar)) {
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
            auto driver = context.alloc.emplace<ValueDriver>(driverKind, **it, analyzedSymbol,
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
            context.manager->getFunctionDrivers(*call, analyzedSymbol, visited, drivers);
    }
}

} // namespace slang::analysis
