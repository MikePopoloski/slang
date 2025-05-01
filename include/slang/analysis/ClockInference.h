//------------------------------------------------------------------------------
//! @file ClockInference.h
//! @brief Assertion clock inference support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <span>

#include "slang/util/Util.h"

namespace slang {
class Diagnostic;
}

namespace slang::ast {

class AssertionExpr;
class AssertionInstanceExpression;
class Expression;
class Symbol;
class TimingControl;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisContext;
class AnalyzedProcedure;

/// Various helper methods for inferring clocks in assertions and checkers.
class SLANG_EXPORT ClockInference {
public:
    /// Helper method that returns true if the given expression is a call to the
    /// $inferred_clock system function.
    static bool isInferredClockCall(const ast::Expression& expr);

    /// Helper method that returns true if the given expression is a call to
    /// one of the sampled value system functions.
    static bool isSampledValueFuncCall(const ast::Expression& expr);

    struct InferredClockResult {
        not_null<const ast::TimingControl*> clock;
        Diagnostic* diag = nullptr;

        InferredClockResult(const ast::TimingControl& clock) : clock(&clock) {}
        InferredClockResult(const ast::TimingControl& clock, Diagnostic* diag) :
            clock(&clock), diag(diag) {}
    };

    struct ExpansionInstance {
        const ast::AssertionInstanceExpression* expr = nullptr;
        const ast::TimingControl* clock = nullptr;
        bool hasInferredClockArg = false;

        ExpansionInstance(const ast::AssertionInstanceExpression& expr,
                          const ast::TimingControl* clock);
    };

    /// Expands inferred clocking events in the given timing control expression.
    static InferredClockResult expand(AnalysisContext& context, const ast::Symbol& parentSymbol,
                                      const ast::TimingControl& timing,
                                      std::span<const ExpansionInstance> expansionStack,
                                      const AnalyzedProcedure* parentProcedure);

    /// Checks the given expression for calls to sampled value functions and
    /// ensures that they have explicit clocking provided.
    static void checkSampledValueFuncs(AnalysisContext& context, const ast::Symbol& parentSymbol,
                                       const ast::Expression& expr);

    /// Checks the given timing control for calls to sampled value functions and
    /// ensures that they have explicit clocking provided.
    static void checkSampledValueFuncs(AnalysisContext& context, const ast::Symbol& parentSymbol,
                                       const ast::TimingControl& timing);

private:
    ClockInference() = delete;
};

} // namespace slang::analysis
