//------------------------------------------------------------------------------
// CaseDecisionDag.cpp
// Decision DAG for case exhaustiveness analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/CaseDecisionDag.h"

#include <numeric>

namespace slang::analysis {

CaseDecisionDag::CaseDecisionDag(std::span<const SVInt> clauses, uint32_t bitWidth, bool wildcardX,
                                 uint32_t maxSteps) {
    SLANG_ASSERT(bitWidth > 0);

    std::vector<ClauseIndex> activeIndices(clauses.size());
    std::iota(activeIndices.begin(), activeIndices.end(), 0);

#if defined(SLANG_DEBUG)
    for (auto& clause : clauses)
        SLANG_ASSERT(clause.getBitWidth() == bitWidth);
#endif

    SVInt start(bitWidth, 0, false);
    build(0, clauses, bitWidth, wildcardX, maxSteps, start, std::move(activeIndices));

    if (steps >= maxSteps) {
        gaveUp = true;
        return;
    }

    // Any clauses not used are marked as redundant.
    for (size_t i = 0; i < clauses.size(); i++) {
        auto index = (ClauseIndex)i;
        if (usedIndices.find(index) == usedIndices.end())
            unreachableClauses.insert(index);
    }

    // Remove overlapping clauses that are fully unreachable.
    erase_if(overlappingClauses, [&](const auto& pair) {
        return unreachableClauses.contains(pair.first) || unreachableClauses.contains(pair.second);
    });
}

void CaseDecisionDag::build(uint32_t level, std::span<const SVInt> clauses, uint32_t bitWidth,
                            bool wildcardX, uint32_t maxSteps, SVInt curPath,
                            std::vector<ClauseIndex>&& activeIndicesInput) {
    if (++steps >= maxSteps)
        return;

    // Check whether we've already observed a substructure identical
    // to this one, and if so skip visiting it again.
    auto [memoIt, inserted] = visitedKeys.emplace(level, std::move(activeIndicesInput));
    if (!inserted)
        return;

    const auto& activeIndices = memoIt->second;
    if (level == bitWidth) {
        if (activeIndices.empty()) {
            // No clauses cover this path, so we have a counterexample.
            if (!counterexample)
                counterexample = curPath;
        }
        else {
            usedIndices.insert(activeIndices[0]);
            for (size_t i = 0; i < activeIndices.size(); i++) {
                for (size_t j = i + 1; j < activeIndices.size(); j++)
                    overlappingClauses.insert({activeIndices[i], activeIndices[j]});
            }
        }
        return;
    }

    // Filter indices to only those that are active at this level given
    // the next character of each clause.
    std::vector<ClauseIndex> falseIndices, trueIndices;
    for (auto index : activeIndices) {
        const auto p = clauses[index][int32_t(bitWidth - level - 1)];
        if (exactlyEqual(p, logic_t(0)))
            falseIndices.push_back(index);
        else if (exactlyEqual(p, logic_t(1)))
            trueIndices.push_back(index);
        else if (exactlyEqual(p, logic_t::z) || (wildcardX && exactlyEqual(p, logic_t::x))) {
            // If we have a wildcard, we need to check both branches.
            falseIndices.push_back(index);
            trueIndices.push_back(index);
        }
    }

    // Recurse down into both sides of the tree at the next level.
    // If we already have a counterexample don't bother manipulating
    // the current path any further.
    if (counterexample) {
        build(level + 1, clauses, bitWidth, wildcardX, maxSteps, SVInt::Zero,
              std::move(falseIndices));
        build(level + 1, clauses, bitWidth, wildcardX, maxSteps, SVInt::Zero,
              std::move(trueIndices));
    }
    else {
        curPath = curPath.shl(1);
        build(level + 1, clauses, bitWidth, wildcardX, maxSteps, curPath, std::move(falseIndices));
        build(level + 1, clauses, bitWidth, wildcardX, maxSteps, curPath | SVInt::One,
              std::move(trueIndices));
    }
}

} // namespace slang::analysis
