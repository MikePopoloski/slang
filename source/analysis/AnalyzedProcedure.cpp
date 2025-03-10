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

AnalyzedProcedure::AnalyzedProcedure(AnalysisContext& context, const Symbol& analyzedSymbol,
                                     const AnalyzedProcedure* parentProcedure) :
    analyzedSymbol(&analyzedSymbol), parentProcedure(parentProcedure) {

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

        if (!dfa.getAssertionStatements().empty() || parentProcedure) {
            inferredClock = dfa.inferClock(parentProcedure);
            if (!inferredClock) {
                auto scope = procedure.getParentScope();
                SLANG_ASSERT(scope);

                if (auto defaultClocking = scope->getCompilation().getDefaultClocking(*scope))
                    inferredClock = &defaultClocking->as<ClockingBlockSymbol>().getEvent();
            }

            if (inferredClock && inferredClock->bad())
                return;

            for (auto stmt : dfa.getAssertionStatements()) {
                if (stmt->kind == StatementKind::ProceduralChecker) {
                    for (auto inst : stmt->as<ProceduralCheckerStatement>().instances)
                        assertions.emplace_back(context, inferredClock, *this, *stmt, inst);
                }
                else {
                    assertions.emplace_back(context, inferredClock, *this, *stmt, nullptr);
                }
            }
        }
    }
}

} // namespace slang::analysis
