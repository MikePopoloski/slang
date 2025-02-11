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
class TimingControl;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisContext;
class AnalysisManager;

class SLANG_EXPORT AnalyzedProcedure {
public:
    not_null<const ast::ProceduralBlockSymbol*> procedureSymbol;

    AnalyzedProcedure(AnalysisManager& analysisManager, AnalysisContext& context,
                      const ast::ProceduralBlockSymbol& symbol);

    const ast::TimingControl* getInferredClock() const { return inferredClock; }

private:
    const ast::TimingControl* inferredClock = nullptr;
};

} // namespace slang::analysis
