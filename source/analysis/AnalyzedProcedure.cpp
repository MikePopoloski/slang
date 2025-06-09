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
            dfa.visitLatches([&](const Symbol&, const Expression& expr) {
                FormatBuffer buffer;
                LSPUtilities::stringifyLSP(expr, dfa.getEvalContext(), buffer);

                context.addDiag(procedure, diag::InferredLatch, expr.sourceRange) << buffer.str();
            });
        }
        else if (procedure.procedureKind == ProceduralBlockKind::AlwaysLatch) {
            bool anyLatchInferred = false;
            dfa.visitLatches([&](const Symbol&, const Expression&) { anyLatchInferred = true; });
            if (!anyLatchInferred)
                context.addDiag(procedure, diag::InferredNoLatch, procedure.location);
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
            addFunctionDrivers(context, *call, visited);
    }
}

void AnalyzedProcedure::addFunctionDrivers(AnalysisContext& context, const CallExpression& expr,
                                           SmallSet<const SubroutineSymbol*, 2>& visited) {
    if (expr.isSystemCall() || expr.thisClass() ||
        expr.getSubroutineKind() != SubroutineKind::Function) {
        return;
    }

    auto& subroutine = *std::get<const SubroutineSymbol*>(expr.subroutine);
    if (subroutine.flags.has(MethodFlags::Pure | MethodFlags::InterfaceExtern |
                             MethodFlags::DPIImport | MethodFlags::Randomize |
                             MethodFlags::BuiltIn)) {
        return;
    }

    // The contents of non-static class methods don't get propagated up
    // to the caller.
    auto subroutineParent = subroutine.getParentScope();
    SLANG_ASSERT(subroutineParent);
    if (subroutineParent->asSymbol().kind == SymbolKind::ClassType) {
        if (!subroutine.flags.has(MethodFlags::Static))
            return;
    }

    // If we've already visited this function then we don't need to
    // analyze it again.
    if (!visited.insert(&subroutine).second)
        return;

    // Get analysis for the function.
    auto analysis = context.manager->getAnalyzedSubroutine(subroutine);
    if (!analysis) {
        auto proc = std::make_unique<AnalyzedProcedure>(context, subroutine);
        analysis = context.manager->addAnalyzedSubroutine(subroutine, std::move(proc));
    }

    // For each driver in the function, create a new driver that points to the
    // original driver but has the current procedure as the containing symbol.
    auto funcDrivers = analysis->getDrivers();
    drivers.reserve(drivers.size() + funcDrivers.size());

    auto& options = context.manager->getOptions();
    for (auto& [valueSym, driverList] : funcDrivers) {
        // The user can disable this inlining of drivers for function locals via a flag.
        if (options.flags.has(AnalysisFlags::AllowMultiDrivenLocals)) {
            auto scope = valueSym->getParentScope();
            while (scope && scope->asSymbol().kind == SymbolKind::StatementBlock)
                scope = scope->asSymbol().getParentScope();

            if (scope == &subroutine)
                continue;
        }

        DriverList perSymbol;
        for (auto& [driver, bounds] : driverList) {
            auto newDriver = context.alloc.emplace<ValueDriver>(driver->kind,
                                                                *driver->prefixExpression,
                                                                *analyzedSymbol, DriverFlags::None);
            newDriver->procCallExpression = &expr;

            perSymbol.emplace_back(newDriver, bounds);
        }

        drivers.emplace_back(valueSym, std::move(perSymbol));
    }

    // If this function has any calls, we need to recursively add drivers
    // from those calls as well.
    for (auto call : analysis->getCallExpressions())
        addFunctionDrivers(context, *call, visited);
}

} // namespace slang::analysis
