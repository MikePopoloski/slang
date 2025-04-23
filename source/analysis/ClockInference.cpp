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
#include "slang/ast/ASTVisitor.h"
#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

using namespace ast;
using parsing::KnownSystemName;

ClockInference::ExpansionInstance::ExpansionInstance(const AssertionInstanceExpression& expr,
                                                     const TimingControl* clock) :
    expr(&expr), clock(clock) {

    // Determine if this instance has an inferred clocking default argument.
    for (auto& arg : expr.arguments) {
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
        if (call.getKnownSystemName() == parsing::KnownSystemName::InferredClock)
            return true;
    }
    return false;
}

static const flat_hash_set<KnownSystemName> SampleValueFuncNames = {
    KnownSystemName::Rose, KnownSystemName::Fell, KnownSystemName::Stable, KnownSystemName::Changed,
    KnownSystemName::Past};

bool ClockInference::isSampledValueFuncCall(const Expression& expr) {
    if (expr.kind == ExpressionKind::Call)
        return SampleValueFuncNames.contains(expr.as<CallExpression>().getKnownSystemName());
    return false;
}

static const TimingControl* findInferredClock(
    const Symbol& target, const Symbol& currSymbol,
    std::span<const ClockInference::ExpansionInstance> expansionStack,
    const AnalyzedProcedure* parentProcedure) {

    for (auto inst : std::views::reverse(expansionStack)) {
        if (&target == &inst.expr->symbol)
            return inst.clock;
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
        for (auto event : timing.as<EventListControl>().events) {
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

struct SampledValueFuncVisitor {
    AnalysisContext& context;
    const Symbol& parentSymbol;

    SampledValueFuncVisitor(AnalysisContext& context, const Symbol& parentSymbol) :
        context(context), parentSymbol(parentSymbol) {}

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<Expression, T>) {
            if (ClockInference::isSampledValueFuncCall(expr)) {
                auto& call = expr.template as<CallExpression>();
                bool hasClock;
                if (call.getKnownSystemName() == KnownSystemName::Past) {
                    hasClock = call.arguments().size() == 4 &&
                               call.arguments()[3]->kind != ExpressionKind::EmptyArgument;
                }
                else {
                    hasClock = call.arguments().size() == 2 &&
                               call.arguments()[1]->kind != ExpressionKind::EmptyArgument;
                }

                if (!hasClock) {
                    context.addDiag(parentSymbol, diag::SampledValueFuncClock, call.sourceRange)
                        << call.getSubroutineName();
                }
            }
            else if constexpr (HasVisitExprs<T, SampledValueFuncVisitor>) {
                expr.visitExprs(*this);
            }
        }
    }
};

void ClockInference::checkSampledValueFuncs(AnalysisContext& context, const Symbol& parentSymbol,
                                            const Expression& expr) {
    SampledValueFuncVisitor visitor{context, parentSymbol};
    expr.visit(visitor);
}

void ClockInference::checkSampledValueFuncs(AnalysisContext& context, const Symbol& parentSymbol,
                                            const TimingControl& timing) {
    if (timing.kind == TimingControlKind::EventList) {
        for (auto& event : timing.as<EventListControl>().events)
            checkSampledValueFuncs(context, parentSymbol, *event);
    }
    else if (timing.kind == TimingControlKind::SignalEvent) {
        auto& sec = timing.as<SignalEventControl>();
        checkSampledValueFuncs(context, parentSymbol, sec.expr);
        if (sec.iffCondition)
            checkSampledValueFuncs(context, parentSymbol, *sec.iffCondition);
    }
}

} // namespace slang::analysis
