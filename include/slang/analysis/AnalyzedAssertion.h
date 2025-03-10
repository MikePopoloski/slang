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

class Statement;
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
    /// The assertion statement that was analyzed.
    not_null<const ast::Statement*> analyzedStatement;

    /// If this assertion is a procedural checker, this is the expanded
    /// analyzed checker body.
    const AnalyzedScope* checkerScope = nullptr;

    /// Constructs a new AnalyzedAssertion object.
    AnalyzedAssertion(AnalysisContext& context, const ast::TimingControl* contextualClock,
                      const AnalyzedProcedure& procedure, const ast::Statement& stmt,
                      const ast::Symbol* checkerInstance);
};

} // namespace slang::analysis
