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

AnalyzedProcedure::AnalyzedProcedure(AnalysisManager&, AnalysisContext& context,
                                     const ProceduralBlockSymbol& procedure) {
    DataFlowAnalysis dataFlowAnalysis(context, procedure);
    dataFlowAnalysis.run(procedure.getBody());
    if (dataFlowAnalysis.bad)
        return;

    if (procedure.procedureKind == ProceduralBlockKind::AlwaysComb) {
        SmallVector<std::pair<const Symbol*, const Expression*>> partiallyAssigned;
        dataFlowAnalysis.getPartiallyAssignedSymbols(partiallyAssigned);

        for (auto [symbol, expr] : partiallyAssigned) {
            // Skip automatic variables, which can't be inferred latches.
            if (VariableSymbol::isKind(symbol->kind) &&
                symbol->as<VariableSymbol>().lifetime == VariableLifetime::Automatic) {
                continue;
            }
            context.diagnostics.add(procedure, diag::InferredLatch, expr->sourceRange)
                << symbol->name;
        }
    }
}

} // namespace slang::analysis
