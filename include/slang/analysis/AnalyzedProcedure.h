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

/// Represents an analyzed procedure.
class SLANG_EXPORT AnalyzedProcedure {
public:
    /// The symbol that was analyzed.
    not_null<const ast::ProceduralBlockSymbol*> procedureSymbol;

    /// Constructs a new AnalyzedProcedure object.
    AnalyzedProcedure(AnalysisManager& analysisManager, AnalysisContext& context,
                      const ast::ProceduralBlockSymbol& symbol);

    /// Returns the inferred clocking block for the procedure, if available.
    ///
    /// @note Clock inference is only performed if the procedure contains
    /// at least one concurrent assertion.
    const ast::TimingControl* getInferredClock() const { return inferredClock; }

private:
    const ast::TimingControl* inferredClock = nullptr;
};

} // namespace slang::analysis
