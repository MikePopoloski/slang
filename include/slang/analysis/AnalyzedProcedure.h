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
#include "slang/util/SmallMap.h"
#include "slang/util/Util.h"

namespace slang::ast {

class CallExpression;
class SubroutineSymbol;
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

    /// Gets all of the subroutine calls in the procedure.
    std::span<const ast::CallExpression* const> getCallExpressions() const {
        return callExpressions;
    }

private:
    void addFunctionDrivers(AnalysisContext& context, const ast::CallExpression& expr,
                            SmallSet<const ast::SubroutineSymbol*, 2>& visited);

    const ast::TimingControl* inferredClock = nullptr;
    std::vector<SymbolDriverListPair> drivers;
    std::vector<AnalyzedAssertion> assertions;
    std::vector<const ast::CallExpression*> callExpressions;
};

} // namespace slang::analysis
