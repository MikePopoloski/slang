//------------------------------------------------------------------------------
// NonProceduralExprVisitor.h
// Internal visitor for analyzing a non-procedural expression
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/analysis/AnalysisManager.h"
#include "slang/analysis/ClockInference.h"
#include "slang/ast/ASTVisitor.h"

namespace slang::analysis {

using namespace ast;

// For non-procedural expressions, we visit them with this visitor to
// perform various checks.
struct NonProceduralExprVisitor {
    AnalysisContext& context;
    const Symbol& containingSymbol;

    NonProceduralExprVisitor(AnalysisContext& context, const Symbol& containingSymbol) :
        context(context), containingSymbol(containingSymbol) {}

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_same_v<T, CallExpression>) {
            if (ClockInference::isSampledValueFuncCall(expr)) {
                // If we don't have a default clocking active in this scope then
                // we should check the call to be sure it has an explicit clock provided.
                if (getDefaultClocking() == nullptr)
                    ClockInference::checkSampledValueFuncs(context, containingSymbol, expr);
            }
        }
        else if constexpr (std::is_same_v<T, AssertionInstanceExpression>) {
            // We might want to find a place to store these analyzed assertions created in
            // non-procedural contexts, but for now it's enough to make sure they're valid.
            AnalyzedAssertion(context, getDefaultClocking(), nullptr, containingSymbol, expr);
        }

        if constexpr (HasVisitExprs<T, NonProceduralExprVisitor>) {
            expr.visitExprs(*this);
        }
    }

private:
    const TimingControl* getDefaultClocking() const {
        auto scope = containingSymbol.getParentScope();
        SLANG_ASSERT(scope);

        if (auto defClk = scope->getCompilation().getDefaultClocking(*scope))
            return &defClk->as<ClockingBlockSymbol>().getEvent();

        return nullptr;
    }
};

} // namespace slang::analysis
