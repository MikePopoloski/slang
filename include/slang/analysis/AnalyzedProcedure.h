//------------------------------------------------------------------------------
//! @file AnalyzedProcedure.h
//! @brief Analysis support for procedures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

namespace slang::ast {
class ProceduralBlockSymbol;
}

namespace slang::analysis {

class AnalysisManager;

class AnalyzedProcedure {
public:
    AnalyzedProcedure(AnalysisManager& analysisManager, const ast::ProceduralBlockSymbol& symbol);
};

} // namespace slang::analysis
