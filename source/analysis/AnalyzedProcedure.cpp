//------------------------------------------------------------------------------
// AnalyzedProcedure.cpp
// Analysis support for procedures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AnalyzedProcedure.h"

#include "slang/analysis/ControlFlowPass.h"

namespace slang::analysis {

using namespace ast;

AnalyzedProcedure::AnalyzedProcedure(AnalysisManager& analysisManager,
                                     const ProceduralBlockSymbol& symbol) {
    ControlFlowPass controlFlowPass(symbol, symbol.getBody());
}

} // namespace slang::analysis
