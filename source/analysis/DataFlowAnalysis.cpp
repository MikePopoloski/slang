//------------------------------------------------------------------------------
// DataFlowAnalysis.cpp
// Data flow analysis pass
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/DataFlowAnalysis.h"

#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

namespace detail {

ExpressionSequenceChecker::ExpressionSequenceChecker(FlowAnalysisBase& base,
                                                     AnalysisContext* context) :
    base(base), context(context) {
    seqTree.push_back(0);
}

void ExpressionSequenceChecker::clear() {
    if (!isEnabled())
        return;

    SLANG_ASSERT(!currFrame);

    seqTree.clear();
    seqTree.push_back(0);
    trackedUses.clear();
    currRegion = 0;
}

void ExpressionSequenceChecker::noteUse(const ValuePath& path, bool isLValue) {
    if (!isEnabled())
        return;

    // If this is an lvalue and we're currently buffering lvalue writes we
    // should simply save it and move on.
    if (isLValue && currFrame) {
        currFrame->lvals.push_back(path);

        // If lvalues also count as rvalue usages in this frame
        // we should register that now.
        if (currFrame->isAlsoRVal)
            checkUsage(path, /* isLValue */ false);
    }
    else {
        // Otherwise just check the usage.
        checkUsage(path, isLValue);
    }
}

void ExpressionSequenceChecker::applyPendingLValues() {
    if (!isEnabled())
        return;

    SLANG_ASSERT(currFrame);
    for (auto& path : currFrame->lvals)
        checkUsage(path, true);
}

void ExpressionSequenceChecker::checkUsage(const ValuePath& path, bool isMod) {
    SLANG_ASSERT(path.rootSymbol && path.fullExpr);

    // Loop over all existing uses of this object and see if they conflict,
    // i.e. with two writes or a read+write of the same symbol path.
    bool warned = false;
    auto& vec = trackedUses[path.rootSymbol];
    for (auto& [prevPath, tag] : vec) {
        if (prevPath.overlaps(path)) {
            if (tag.warned)
                return;

            if ((isMod || tag.isMod) && isUnsequenced(tag.seq)) {
                auto code = (isMod && tag.isMod) ? diag::MultiWriteExpr : diag::ReadWriteExpr;
                context->addDiag(base.rootSymbol, code, path.fullExpr->sourceRange)
                    << path.toString(base.getEvalContext()) << prevPath.fullExpr->sourceRange;

                warned = true;
                break;
            }
        }
    }

    vec.emplace_back(path, Tag{.seq = currRegion, .isMod = isMod, .warned = warned});
}

bool ExpressionSequenceChecker::isUnsequenced(uint32_t seq) {
    uint32_t curr = representative(currRegion);
    uint32_t target = representative(seq);
    while (curr >= target) {
        if (curr == target)
            return true;
        curr = seqTree[curr].parent;
    }
    return false;
}

uint32_t ExpressionSequenceChecker::representative(uint32_t seq) {
    // Pick a representative sequence region. If the given
    // region has been merged we will compactify up the parent
    // chain as we go, looking for an unmerged region (which we
    // will always find since the root is never merged).
    if (seqTree[seq].merged)
        return seqTree[seq].parent = representative(seqTree[seq].parent);
    return seq;
}

} // namespace detail

} // namespace slang::analysis
