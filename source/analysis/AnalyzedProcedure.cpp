//------------------------------------------------------------------------------
// AnalyzedProcedure.cpp
// Analysis support for procedures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AnalyzedProcedure.h"

#include "slang/analysis/DataFlowAnalysis.h"

namespace slang::analysis {

using namespace ast;

AnalyzedProcedure::AnalyzedProcedure(AnalysisManager& analysisManager, AnalysisContext& context,
                                     const ProceduralBlockSymbol& symbol) {
    DataFlowAnalysis dataFlowAnalysis(context, symbol, symbol.getBody());
}

} // namespace slang::analysis
