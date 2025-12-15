//------------------------------------------------------------------------------
//! @file AnalyzedAssertion.h
//! @brief Analysis support for concurrent assertions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/FlatMap.h"
#include "slang/util/Util.h"

namespace slang::ast {

class AssertionExpr;
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
    /// The symbol that contains this assertion.
    not_null<const ast::Symbol*> containingSymbol;

    /// The procedure that contains this assertion, if any.
    const AnalyzedProcedure* procedure = nullptr;

    /// The AST node that describes the assertion.
    std::variant<const ast::ConcurrentAssertionStatement*, const ast::AssertionInstanceExpression*>
        astNode;

    /// Set to true if there was an error analyzing the assertion.
    bool bad = false;

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

    /// Gets the root of the assertion expression tree.
    const ast::AssertionExpr& getRoot() const;

    /// Gets the semantic leading clock of the assertion.
    const ast::TimingControl* getSemanticLeadingClock() const;

    /// Gets the clock that applies to the given sub-expression of this assertion.
    ///
    /// @note Returns nullptr if the given expression is multi-clocked, meaning you
    /// must examine its subexpressions to know how to evaluate the full expression.
    const ast::TimingControl* getClock(const ast::AssertionExpr& expr) const;

private:
    friend struct AssertionVisitor;

    const ast::TimingControl* firstClock = nullptr;
    flat_hash_map<const ast::AssertionExpr*, const ast::TimingControl*> clocksForExpr;
};

} // namespace slang::analysis
