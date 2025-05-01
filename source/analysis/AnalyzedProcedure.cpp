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

    canCache = !dfa.sawRecursiveFunction;
    if (dfa.bad)
        return;

    if (parentProcedure || !dfa.getAssertions().empty() || !dfa.getSampledValueCalls().empty()) {
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

        for (auto& var : dfa.getAssertions()) {
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
        if (!inferredClock) {
            for (auto call : dfa.getSampledValueCalls())
                ClockInference::checkSampledValueFuncs(context, analyzedSymbol, *call);
        }
    }

    if (analyzedSymbol.kind == SymbolKind::ProceduralBlock) {
        auto& procedure = analyzedSymbol.as<ProceduralBlockSymbol>();
        if (procedure.procedureKind == ProceduralBlockKind::AlwaysComb) {
            dfa.visitLatches([&](const Symbol&, const Expression& expr) {
                FormatBuffer buffer;
                stringifyLSP(expr, dfa.getEvalContext(), buffer);

                context.addDiag(procedure, diag::InferredLatch, expr.sourceRange) << buffer.str();
            });
        }
    }
    else if (analyzedSymbol.kind == SymbolKind::Subroutine) {
        // Diagnose missing return statements and/or incomplete
        // assignments to the return value var.
        auto& subroutine = analyzedSymbol.as<SubroutineSymbol>();
        if (dfa.isReachable() && subroutine.subroutineKind == SubroutineKind::Function &&
            !subroutine.getReturnType().isVoid() && !subroutine.name.empty()) {

            // Control falls off the end of a non-void function but that is
            // fine if the return value var is definitely assigned here.
            SLANG_ASSERT(subroutine.returnValVar);
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
                                                             AssignFlags::None);
            perSymbol.emplace_back(driver, bounds);
        }

        drivers.emplace_back(&symbol, std::move(perSymbol));
    }

    for (auto& [_, symDriverList] : dfa.getIndirectDrivers()) {
        drivers.reserve(drivers.size() + symDriverList.size());
        for (auto& [valueSym, driverList] : symDriverList)
            drivers.emplace_back(valueSym, driverList);
    }
}

} // namespace slang::analysis
