//------------------------------------------------------------------------------
//! @file TautologicalCompare.h
//! @brief Checks for comparisons that always evaluate to the same result
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Util.h"

namespace slang::ast {

class BinaryExpression;
class Symbol;

} // namespace slang::ast

namespace slang::analysis {

class AnalysisContext;

/// Lint checks for comparisons (and logical combinations of comparisons)
/// whose result can be determined without knowing the runtime values involved,
/// which almost always indicates a bug.
class SLANG_EXPORT TautologicalCompare {
public:
    /// Checks the given binary expression and reports any tautological comparisons
    /// found to the given analysis context. Only the given expression itself is
    /// examined; callers are expected to invoke this for each nested binary expression.
    static void check(AnalysisContext& context, const ast::Symbol& rootSymbol,
                      const ast::BinaryExpression& expr);
};

} // namespace slang::analysis
