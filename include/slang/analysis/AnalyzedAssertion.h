//------------------------------------------------------------------------------
//! @file AnalyzedAssertion.h
//! @brief Analysis support for concurrent assertions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang::ast {

class AssertionInstanceExpression;
class ConcurrentAssertionStatement;
class Symbol;
class TimingControl;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisContext;
class AnalyzedProcedure;
class AnalyzedScope;

/// Represents an analyzed assertion (or procedural checker).
class SLANG_EXPORT AnalyzedAssertion {
public:
    /// Constructs a new AnalyzedAssertion object.
    AnalyzedAssertion(AnalysisContext& context, const AnalyzedProcedure& procedure,
                      const ast::ConcurrentAssertionStatement& stmt);

    /// Constructs a new AnalyzedAssertion object.
    AnalyzedAssertion(AnalysisContext& context, const AnalyzedProcedure& procedure,
                      const ast::AssertionInstanceExpression& expr);

    /// Constructs a new AnalyzedAssertion object.
    AnalyzedAssertion(AnalysisContext& context, const ast::TimingControl* contextualClock,
                      const ast::Symbol& parentSymbol,
                      const ast::AssertionInstanceExpression& expr);
};

} // namespace slang::analysis
