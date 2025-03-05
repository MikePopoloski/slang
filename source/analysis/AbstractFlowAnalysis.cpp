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

} // namespace slang::analysis
