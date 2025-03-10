//------------------------------------------------------------------------------
//! @file AnalyzedProcedure.h
//! @brief Analysis support for procedures
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <span>
#include <vector>

#include "slang/analysis/AnalyzedAssertion.h"
#include "slang/util/Util.h"

namespace slang::ast {

class Symbol;
class TimingControl;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisContext;

/// Represents an analyzed procedure.
class SLANG_EXPORT AnalyzedProcedure {
public:
    /// The symbol that was analyzed.
    not_null<const ast::Symbol*> analyzedSymbol;

    /// The procedure that contains this one, if any.
    /// Only possible for procedural checker instances.
    const AnalyzedProcedure* parentProcedure;

    /// Constructs a new AnalyzedProcedure object.
    AnalyzedProcedure(AnalysisContext& context, const ast::Symbol& symbol,
                      const AnalyzedProcedure* parentProcedure = nullptr);

    /// Returns the inferred clocking block for the procedure, if available.
    ///
    /// @note Clock inference is only performed if the procedure contains
    /// at least one concurrent assertion.
    const ast::TimingControl* getInferredClock() const { return inferredClock; }

    /// Gets the list of analyzed assertions in the procedure.
    ///
    /// @note These include procedural checkers contained within the procedure.
    std::span<const AnalyzedAssertion> getAssertions() const { return assertions; }

private:
    const ast::TimingControl* inferredClock = nullptr;
    std::vector<AnalyzedAssertion> assertions;
};

} // namespace slang::analysis
