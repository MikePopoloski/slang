//------------------------------------------------------------------------------
// DataFlowAnalysis.cpp
// Data flow analysis pass
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/DataFlowAnalysis.h"

#include <bit>

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
    currRegion = 0;

    for (auto& [symbol, map] : trackedUses)
        map.clear(context->taggedLSPAlloc);
    trackedUses.clear();
}

void ExpressionSequenceChecker::noteUse(const ValueSymbol& symbol, DriverBitRange bounds,
                                        const Expression& lsp, bool isLValue) {
    if (!isEnabled())
        return;

    // If this is an lvalue and we're currently buffering lvalue writes we
    // should simply save it and move on.
    if (isLValue && currFrame) {
        currFrame->lvals.push_back({&symbol, bounds, &lsp});

        // If lvalues also count as rvalue usages in this frame
        // we should register that now.
        if (currFrame->isAlsoRVal)
            checkUsage(symbol, bounds, lsp, /* isLValue */ false);
    }
    else {
        // Otherwise just check the usage.
        checkUsage(symbol, bounds, lsp, isLValue);
    }
}

void ExpressionSequenceChecker::applyPendingLValues() {
    if (!isEnabled())
        return;

    SLANG_ASSERT(currFrame);
    for (auto& [symbol, bounds, lsp] : currFrame->lvals)
        checkUsage(*symbol, bounds, *lsp, true);
}

void ExpressionSequenceChecker::checkUsage(const ValueSymbol& symbol, DriverBitRange bounds,
                                           const Expression& lsp, bool isMod) {
    struct Tag {
        uint32_t seq : 30;
        bool isMod : 1;
        bool warned : 1;
    };
    static_assert(sizeof(Tag) == sizeof(uint32_t));
    static_assert(std::has_unique_object_representations_v<Tag>);

    // Loop over all existing uses of this object and see if they conflict,
    // i.e. with two writes or a read+write of the same symbol / LSP.
    bool warned = false;
    auto& map = trackedUses[&symbol];
    auto end = map.end();
    for (auto it = map.find(bounds); it != end; ++it) {
        const Tag tag = std::bit_cast<Tag, uint32_t>((*it).second);
        if (tag.warned)
            return;

        if ((isMod || tag.isMod) && isUnsequenced(tag.seq)) {
            FormatBuffer buffer;
            LSPUtilities::stringifyLSP(lsp, base.getEvalContext(), buffer);

            auto code = (isMod && tag.isMod) ? diag::MultiWriteExpr : diag::ReadWriteExpr;
            context->addDiag(base.rootSymbol, code, lsp.sourceRange)
                << buffer.str() << (*it).first->sourceRange;

            warned = true;
            break;
        }
    }

    Tag newTag{.seq = currRegion, .isMod = isMod, .warned = warned};
    map.insert(bounds, {&lsp, std::bit_cast<uint32_t, Tag>(newTag)}, context->taggedLSPAlloc);
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
