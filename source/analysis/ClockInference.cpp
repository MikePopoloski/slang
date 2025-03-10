//------------------------------------------------------------------------------
// ClockInference.cpp
// Assertion clock inference support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/ClockInference.h"

#include "slang/analysis/AnalysisManager.h"
#include "slang/analysis/AnalyzedProcedure.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

using namespace ast;

ClockInference::ExpansionInstance::ExpansionInstance(const AssertionExpr& expr,
                                                     const TimingControl* clock) :
    expr(&expr), clock(clock) {

    // Determine if this instance has an inferred clocking default argument.
    auto& aie = expr.as<SimpleAssertionExpr>().expr.as<AssertionInstanceExpression>();
    for (auto& arg : aie.arguments) {
        if (auto argExpr = std::get_if<const Expression*>(&std::get<1>(arg))) {
            if (ClockInference::isInferredClockCall(**argExpr)) {
                hasInferredClockArg = true;
                break;
            }
        }
    }
}

bool ClockInference::isInferredClockCall(const Expression& expr) {
    if (expr.kind == ExpressionKind::Call) {
        auto& call = expr.as<CallExpression>();
        if (call.isSystemCall() && call.getSubroutineName() == "$inferred_clock")
            return true;
    }
    return false;
}

static const TimingControl* findInferredClock(
    const Symbol& target, const Symbol& currSymbol,
    std::span<const ClockInference::ExpansionInstance> expansionStack,
    const AnalyzedProcedure* parentProcedure) {

    for (auto inst : std::views::reverse(expansionStack)) {
        if (&target ==
            &inst.expr->as<SimpleAssertionExpr>().expr.as<AssertionInstanceExpression>().symbol) {
            return inst.clock;
        }
    }

    if (parentProcedure) {
        // We can be called either with a parentProcedure that is a procedural block
        // containing our assertion, or with a parentProcedure that is a procedural
        // block containing a parent checker instance. This lookup here only wants
        // to deal with finding checker formals, so if we're in the first case try
        // looking upward again to find a checker.
        if (parentProcedure->parentProcedure) {
            // This is only ever true when we're in a procedural checker,
            // so go ahead and return the containing procedure's inferred clock.
            parentProcedure = parentProcedure->parentProcedure;
            return parentProcedure->getInferredClock();
        }

        // Otherwise if we're in a regular procedure within a procedural checker
        // we can refer to that checker's formal args, which can have the
        // inferred_clock call.
        auto scope = currSymbol.getParentScope();
        SLANG_ASSERT(scope);
        if (scope->asSymbol().kind == SymbolKind::CheckerInstanceBody)
            return parentProcedure->getInferredClock();
    }

    return nullptr;
}

ClockInference::InferredClockResult ClockInference::expand(
    AnalysisContext& context, const Symbol& parentSymbol, const TimingControl& timing,
    std::span<const ExpansionInstance> expansionStack, const AnalyzedProcedure* parentProcedure) {

    auto& alloc = context.alloc;
    if (timing.kind == TimingControlKind::EventList) {
        SmallVector<const TimingControl*> events;
        for (auto& event : timing.as<EventListControl>().events) {
            auto result = expand(context, parentSymbol, *event, expansionStack, parentProcedure);
            if (result.clock->bad())
                return result;

            events.push_back(result.clock);
        }

        return *alloc.emplace<EventListControl>(events.copy(alloc), timing.sourceRange);
    }

    if (timing.kind == TimingControlKind::SignalEvent) {
        auto& sec = timing.as<SignalEventControl>();
        if (isInferredClockCall(sec.expr)) {
            // Try to find the source of the inferred_clock call; there can be
            // multiple layers of checker, sequence, and property expansion, each
            // with their own defaulted argument with an inferred_clock call.
            auto& targetScope = *std::get<1>(sec.expr.as<CallExpression>().subroutine).scope;
            auto clock = findInferredClock(targetScope.asSymbol(), parentSymbol, expansionStack,
                                           parentProcedure);
            if (!clock) {
                auto& diag = context.addDiag(parentSymbol, diag::NoInferredClock,
                                             sec.expr.sourceRange);
                return {*alloc.emplace<InvalidTimingControl>(&timing), &diag};
            }

            return *clock;
        }
    }

    return timing;
}

} // namespace slang::analysis
