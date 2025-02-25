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

class ConcurrentAssertionStatement;
class Symbol;
class TimingControl;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisContext;

/// Represents an analyzed assertion.
class SLANG_EXPORT AnalyzedAssertion {
public:
    /// The assertion statement that was analyzed.
    not_null<const ast::ConcurrentAssertionStatement*> analyzedStatement;

    /// Constructs a new AnalyzedAssertion object.
    AnalyzedAssertion(AnalysisContext& context, const ast::TimingControl* contextualClock,
                      const ast::Symbol& parentSymbol,
                      const ast::ConcurrentAssertionStatement& stmt);
};

} // namespace slang::analysis
