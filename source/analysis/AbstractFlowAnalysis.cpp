//------------------------------------------------------------------------------
// AbstractFlowAnalysis.cpp
// Base class for flow analysis passes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AbstractFlowAnalysis.h"

namespace slang::analysis {

ConstantValue FlowAnalysisBase::tryEvalBool(const Expression& expr) const {
    return expr.eval(evalContext);
}

bool FlowAnalysisBase::willIterateAtLeastOnce(std::span<const VariableSymbol* const> loopVars,
                                              const Expression& stopExpr) const {
    // We can't know for sure whether the loop will actually execute in all
    // cases, but we can check for a simple case where we have an in-line
    // loop variable(s) that pass the stop condition on the first iteration.
    EvalContext speculativeCtx(evalContext);
    speculativeCtx.pushEmptyFrame();

    for (auto var : loopVars) {
        ConstantValue cv;
        if (auto init = var->getInitializer()) {
            cv = init->eval(speculativeCtx);
            if (!cv)
                return false;
        }

        speculativeCtx.createLocal(var, std::move(cv));
    }

    return stopExpr.eval(speculativeCtx).isTrue();
}

static bool isFullyCoveredWildcards(const SmallVector<SVInt>& patterns, bool wildcardX) {
    for (auto bit : {logic_t(0), logic_t(1)}) {
        // For each branch at the current index (e.g. 0, 1) filter the patterns
        // to only those that can match the chosen bit.
        bool done = false;
        SmallVector<SVInt> nextPatterns;
        for (auto& pattern : patterns) {
            const auto width = pattern.getBitWidth();
            const auto p = pattern[int32_t(width - 1)];
            if (exactlyEqual(p, bit) || exactlyEqual(p, logic_t::z) ||
                (wildcardX && exactlyEqual(p, logic_t::x))) {
                if (width == 1) {
                    done = true;
                    break;
                }
                nextPatterns.emplace_back(pattern.trunc(width - 1));
            }
        }

        // If no pattern can match then the entire branch is uncovered,
        // unless we're at the final bit position in which case we did
        // find a whole match.
        if (nextPatterns.empty()) {
            if (done)
                continue;
            return false;
        }

        // Recurse to the next bit position.
        if (!isFullyCoveredWildcards(nextPatterns, wildcardX))
            return false;
    }
    return true;
}

bool FlowAnalysisBase::isFullyCovered(const CaseStatement& stmt) const {
    // First of all, if the case statement asserts it has full coverage,
    // and our flags allow it, assume full coverage without checking.
    if (flags.has(AnalysisFlags::FullCaseUniquePriority) &&
        (stmt.check == UniquePriorityCheck::Unique ||
         stmt.check == UniquePriorityCheck::Priority)) {
        return true;
    }

    // If the case type is not integral then we can never fully satisfy the condition.
    auto& caseType = *stmt.expr.type;
    if (!caseType.isIntegral())
        return false;

    // TODO: handle case condition being a constant
    if (stmt.expr.eval(evalContext))
        return false;

    // TODO: handle case inside
    if (stmt.condition == CaseStatementCondition::Inside)
        return false;

    const bitwidth_t bitWidth = stmt.expr.unwrapImplicitConversions().type->getBitWidth();

    // TODO: merge with dup checking in ConditionalStatements.cpp
    SmallSet<ConstantValue, 4> seen;
    SmallVector<SVInt> values;
    for (auto& g : stmt.items) {
        for (auto item : g.expressions) {
            auto cv = item->eval(evalContext);
            if (!cv)
                return false;

            if (seen.emplace(cv).second)
                values.emplace_back(std::move(cv).integer());
        }
    }

    // TODO: warn for wildcard case statements with 2-state type?
    if (stmt.condition == CaseStatementCondition::Normal || !caseType.isFourState()) {
        // The number of non-duplicate elements needs to match the number
        // of possible values for the case expression. This depends on
        // whether the type is 2-state or 4-state.
        if (caseType.isFourState() && flags.has(AnalysisFlags::FullCaseFourState))
            return bitWidth < 16 && values.size() >= (size_t)std::pow(4, bitWidth);
        else
            return bitWidth < 32 && values.size() >= (1ull << bitWidth);
    }

    // If we're checking for four-state wildcard coverage we simply need to
    // find an entry that is all Z bits. This is because Z is always a wildcard,
    // so the only way to specify an entry that hits all Z's will also cover
    // all other bits too.
    if (flags.has(AnalysisFlags::FullCaseFourState)) {
        for (auto& val : values) {
            if (val.countLeadingZs() >= bitWidth)
                return true;
        }
        return false;
    }

    // Otherwise do the full wildcard coverage search.
    return isFullyCoveredWildcards(values, stmt.condition == CaseStatementCondition::WildcardXOrZ);
}

} // namespace slang::analysis
