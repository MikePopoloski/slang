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
#include "slang/analysis/ValueDriver.h"
#include "slang/util/Util.h"

namespace slang::ast {

class Symbol;
class TimingControl;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisContext;

/// Represents an analyzed procedure.
///
/// Note that this can include continuous assignments, which are not
/// technically procedures but are treated as such for analysis purposes.
class SLANG_EXPORT AnalyzedProcedure {
public:
    /// The symbol that was analyzed.
    not_null<const ast::Symbol*> analyzedSymbol;

    /// The procedure that contains this one, if any.
    /// Only possible for procedural checker instances.
    const AnalyzedProcedure* parentProcedure;

    /// Set to true to indicate that the procedure can be cached in
    /// the analysis manager.
    ///
    /// This is currently only set to false when analysis of a subroutine finds that
    /// it is recursive while trying to analyze a calling procedure.
    bool canCache = true;

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

    /// Gets all of the drivers in the procedure.
    std::span<const SymbolDriverListPair> getDrivers() const { return drivers; }

private:
    const ast::TimingControl* inferredClock = nullptr;
    std::vector<SymbolDriverListPair> drivers;
    std::vector<AnalyzedAssertion> assertions;
};

} // namespace slang::analysis
