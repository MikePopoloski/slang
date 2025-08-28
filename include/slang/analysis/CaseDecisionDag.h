//------------------------------------------------------------------------------
//! @file CaseDecisionDag.h
//! @brief Decision DAG for case exhaustiveness analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <span>

#include "slang/numeric/SVInt.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/FlatMap.h"

namespace slang::analysis {

/// A helper class for building a decision DAG (directed acyclic graph) for
/// case statement exhaustiveness analysis.
///
/// The DAG is "built" from a set of case statement clauses, where each clause
/// is an integral constant value.
///
/// The DAG is used to determine if a set of clauses covers all possible
/// input values for a given case expression bit width, as well as to identify
/// overlapping and redundant clauses for issuing diagnostics.
class SLANG_EXPORT CaseDecisionDag {
public:
    using ClauseIndex = uint32_t;

    /// Contains the indices of clauses that are never reachable because
    /// some earlier clause subsumes it.
    flat_hash_set<ClauseIndex> unreachableClauses;

    /// Contains pairs of indices that overlap, meaning that some inputs
    /// match both clauses. Clauses that are deemed unreachable are not
    /// included here.
    flat_hash_set<std::pair<ClauseIndex, ClauseIndex>> overlappingClauses;

    /// If the DAG is not exhaustive, this contains a counterexample that
    /// demonstrates a value that is not covered by any of the clauses.
    /// Otherwise, this is empty.
    std::optional<SVInt> counterexample;

    /// If true, analyzing the case clauses took more than maxSteps and so
    /// the analysis was halted.
    bool gaveUp = false;

    /// Constructs a new case decision DAG.
    CaseDecisionDag(std::span<const SVInt> clauses, uint32_t bitWidth, bool wildcardX,
                    uint32_t maxSteps = UINT32_MAX);

    /// Indicates whether the DAG is exhaustive, meaning that all possible
    /// input values are covered by the case statement clauses.
    bool isExhaustive() const { return !counterexample.has_value(); }
};

} // namespace slang::analysis
