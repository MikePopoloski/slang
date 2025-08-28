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

    std::vector<ClauseIndex> initialIndices(clauses.size());
    std::iota(initialIndices.begin(), initialIndices.end(), 0);

#if defined(SLANG_DEBUG)
    for (auto& clause : clauses)
        SLANG_ASSERT(clause.getBitWidth() == bitWidth);
#endif

    struct StackFrame {
        uint32_t level;
        SVInt curPath;
        std::vector<ClauseIndex> activeIndices;
    };

    std::vector<StackFrame> stack;
    stack.emplace_back(0, SVInt(bitWidth, 0, false), std::move(initialIndices));

    using MemoKey = std::pair<uint32_t, std::vector<ClauseIndex>>;
    flat_hash_set<MemoKey> visitedKeys;
    flat_hash_set<ClauseIndex> usedIndices;
    uint32_t steps = 0;

    while (!stack.empty() && ++steps < maxSteps) {
        auto frame = std::move(stack.back());
        stack.pop_back();

        // Check whether we've already observed a substructure identical
        // to this one, and if so skip visiting it again.
        const uint32_t level = frame.level;
        auto [memoIt, inserted] = visitedKeys.emplace(level, std::move(frame.activeIndices));
        if (!inserted)
            continue;

        const auto& activeIndices = memoIt->second;
        if (level == bitWidth) {
            if (activeIndices.empty()) {
                // No clauses cover this path, so we have a counterexample.
                if (!counterexample)
                    counterexample = frame.curPath;
            }
            else {
                usedIndices.insert(activeIndices[0]);
                for (size_t i = 0; i < activeIndices.size(); i++) {
                    for (size_t j = i + 1; j < activeIndices.size(); j++)
                        overlappingClauses.insert({activeIndices[i], activeIndices[j]});
                }
            }
            continue;
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

        // Push both sides of the tree at the next level onto the stack.
        // If we already have a counterexample don't bother manipulating
        // the current path any further.
        if (counterexample) {
            stack.emplace_back(level + 1, SVInt::Zero, std::move(trueIndices));
            stack.emplace_back(level + 1, SVInt::Zero, std::move(falseIndices));
        }
        else {
            frame.curPath = frame.curPath.shl(1);
            stack.emplace_back(level + 1, frame.curPath | SVInt::One, std::move(trueIndices));
            stack.emplace_back(level + 1, frame.curPath, std::move(falseIndices));
        }
    }

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

} // namespace slang::analysis
