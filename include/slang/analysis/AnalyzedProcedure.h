//------------------------------------------------------------------------------
//! @file AnalyzedProcedure.h
//! @brief Analysis support for procedures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang::ast {
class ProceduralBlockSymbol;
}

namespace slang::analysis {

class AnalysisContext;
class AnalysisManager;

class SLANG_EXPORT AnalyzedProcedure {
public:
    AnalyzedProcedure(AnalysisManager& analysisManager, AnalysisContext& context,
                      const ast::ProceduralBlockSymbol& symbol);
};

} // namespace slang::analysis
