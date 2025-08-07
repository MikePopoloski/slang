//------------------------------------------------------------------------------
// AbstractFlowAnalysis.cpp
// Base class for flow analysis passes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AbstractFlowAnalysis.h"

#include <fmt/core.h>

#include "slang/analysis/CaseDecisionDag.h"
#include "slang/diagnostics/AnalysisDiags.h"

namespace slang::analysis {

FlowAnalysisBase::FlowAnalysisBase(const Symbol& symbol, AnalysisOptions options,
                                   Diagnostics* diagnostics) :
    rootSymbol(symbol), options(options), diagnostics(diagnostics),
    evalContext(ASTContext(*symbol.getParentScope(), LookupLocation::after(symbol))) {

    evalContext.pushEmptyFrame();
}

ConstantValue FlowAnalysisBase::tryEvalBool(const Expression& expr) const {
    return expr.eval(evalContext);
}

FlowAnalysisBase::WillExecute FlowAnalysisBase::tryGetLoopIterValues(
    const ForLoopStatement& stmt, SmallVector<ConstantValue>& values,
    SmallVector<ConstantValue*>& localPtrs) {

    if (stmt.loopVars.empty() || !stmt.stopExpr || stmt.steps.empty())
        return WillExecute::Maybe;

    auto cleanupLocals = ScopeGuard([&] {
        values.clear();
        localPtrs.clear();
        for (auto var : stmt.loopVars)
            evalContext.deleteLocal(var);
    });

    for (auto var : stmt.loopVars) {
        auto init = var->getInitializer();
        if (!init)
            return WillExecute::Maybe;

        auto cv = init->eval(evalContext);
        if (!cv)
            return WillExecute::Maybe;

        localPtrs.push_back(evalContext.createLocal(var, std::move(cv)));
    }

    // Each iteration of this loop will consume the given increment steps,
    // so that nested loops count more heavily against our limit.
    const uint32_t increment = std::max(forLoopSteps, 1u);

    WillExecute willExec = WillExecute::No;
    while (true) {
        auto cv = stmt.stopExpr->eval(evalContext);
        if (!cv)
            return WillExecute::Maybe;

        if (!cv.isTrue())
            break;

        willExec = WillExecute::Yes;

        for (auto local : localPtrs)
            values.emplace_back(*local);

        for (auto step : stmt.steps) {
            if (!step->eval(evalContext))
                return WillExecute::Yes;

            forLoopSteps += increment;
            if (forLoopSteps > options.maxLoopAnalysisSteps)
                return WillExecute::Yes;
        }
    }

    // The only path through the function that doesn't clean up locals
    // is when we found a valid false stop expression in the loop above.
    cleanupLocals.release();
    return willExec;
}

bool FlowAnalysisBase::isFullyCovered(const CaseStatement& stmt, const Statement* knownBranch,
                                      bool isKnown) const {
    // This method determines whether a case statement's items fully cover
    // the input space, so that we know whether the default statement
    // (if there is one) is reachable or not.
    //
    // Also while we're here we will issue some diagnostics for lint issues like
    // overlapping case items and duplicate case items, if this analysis has been
    // configured to report diagnostics.

    const auto& caseType = *stmt.expr.type;
    const auto bitWidth = stmt.expr.unwrapImplicitConversions().type->getBitWidth();
    const auto cond = stmt.condition;
    const bool wildcard = cond == CaseStatementCondition::WildcardXOrZ ||
                          cond == CaseStatementCondition::WildcardJustZ;

    // Collect all constant case values, checking for duplicates and overlaps
    // if we are looking for diagnostics.
    bool hasNonConstItems = false;
    SmallMap<ConstantValue, const Expression*, 4> elems;
    SmallVector<SVInt> intVals;
    SmallVector<const Expression*> itemExpressions;
    for (auto& g : stmt.items) {
        for (auto item : g.expressions) {
            if (auto cv = item->eval(evalContext)) {
                auto [it, inserted] = elems.emplace(std::move(cv), item);
                if (!inserted) {
                    if (diagnostics) {
                        // Don't warn if there is a statically known branch and this duplicate
                        // does not match the known branch's value.
                        if (!isKnown || it->first == stmt.expr.eval(evalContext)) {
                            auto& diag = diagnostics->add(rootSymbol, diag::CaseDup,
                                                          item->sourceRange);
                            diag << SemanticFacts::getCaseConditionStr(cond) << it->first;
                            diag.addNote(diag::NotePreviousUsage, it->second->sourceRange);
                        }
                    }
                }
                else if (it->first.isInteger()) {
                    // Save off the values for later use in building the decision
                    // DAG. One weid thing here: if the value has x bits and we're
                    // not in a casex statement we should ignore the item, since we
                    // won't check for coverage of x bits in the decision DAG and these
                    // clauses will show up as unreachable otherwise.
                    auto& val = it->first.integer();
                    if (cond != CaseStatementCondition::WildcardJustZ || val.countXs() == 0) {
                        intVals.push_back(val.trunc(bitWidth));
                        itemExpressions.push_back(item);
                    }
                }
            }
            else {
                hasNonConstItems = true;
            }

            if (diagnostics && (cond == CaseStatementCondition::Normal ||
                                cond == CaseStatementCondition::WildcardJustZ)) {
                // If we're not in a wildcard case we should warn
                // about integer literal items that have unknown bits.
                // Similarly, if we're in a wildcard case with just Zs
                // we should warn if we see Xs.
                auto& unwrapped = item->unwrapImplicitConversions();
                if (unwrapped.kind == ExpressionKind::IntegerLiteral) {
                    auto& lit = unwrapped.as<IntegerLiteral>();
                    if (cond == CaseStatementCondition::Normal && lit.getValue().hasUnknown()) {
                        diagnostics->add(rootSymbol, diag::CaseNotWildcard, item->sourceRange);
                    }
                    else if (cond == CaseStatementCondition::WildcardJustZ &&
                             lit.getValue().countXs() > 0) {
                        diagnostics->add(rootSymbol, diag::CaseZWithX, item->sourceRange);
                    }
                }
            }
        }
    }

    std::optional<CaseDecisionDag> decisionDag;
    auto makeDecisionDag = [&]() {
        decisionDag.emplace(intVals, bitWidth, cond == CaseStatementCondition::WildcardXOrZ,
                            options.maxCaseAnalysisSteps);
    };

    // If diagnostics are enabled do various lint checks now.
    if (diagnostics) {
        // If the case branch is statically known to not select anything we
        // should warn about that.
        if (isKnown && !knownBranch) {
            auto& diag = diagnostics->add(rootSymbol, diag::CaseNone, stmt.expr.sourceRange);
            diag << stmt.expr.eval(evalContext);
            diag << SemanticFacts::getCaseConditionStr(cond);
        }

        // Check for missing enum coverage.
        if (caseType.isEnum()) {
            SmallVector<std::string_view> missing;
            for (auto& ev : caseType.getCanonicalType().as<EnumType>().values()) {
                auto& val = ev.getValue();
                if (!elems.contains(val))
                    missing.push_back(ev.name);
            }

            if (!missing.empty()) {
                std::string msg;
                if (missing.size() == 1) {
                    msg = fmt::format("value '{}'", missing[0]);
                }
                else if (missing.size() == 2) {
                    msg = fmt::format("values '{}' and '{}'", missing[0], missing[1]);
                }
                else if (missing.size() == 3) {
                    msg = fmt::format("values '{}', '{}', and '{}'", missing[0], missing[1],
                                      missing[2]);
                }
                else {
                    const size_t remainder = missing.size() - 3;
                    msg = fmt::format("values '{}', '{}', '{}' (and {} other{})", missing[0],
                                      missing[1], missing[2], remainder, remainder == 1 ? "" : "s");
                }

                auto code = stmt.defaultCase ? diag::CaseEnumExplicit : diag::CaseEnum;
                diagnostics->add(rootSymbol, code, stmt.expr.sourceRange) << msg;
            }
        }

        // If this is a wildcard case statement check for overlaps.
        if (wildcard) {
            makeDecisionDag();

            if (decisionDag->gaveUp) {
                auto& diag = diagnostics->add(rootSymbol, diag::CaseComplex, stmt.expr.sourceRange);
                diag << SemanticFacts::getCaseConditionStr(cond);
            }
            else {
                if (decisionDag->counterexample && !stmt.defaultCase) {
                    auto& diag = diagnostics->add(rootSymbol, diag::CaseIncomplete,
                                                  stmt.expr.sourceRange);
                    diag << SemanticFacts::getCaseConditionStr(cond);
                    diag << *decisionDag->counterexample;
                }

                for (auto index : decisionDag->unreachableClauses) {
                    auto& diag = diagnostics->add(rootSymbol, diag::CaseUnreachable,
                                                  itemExpressions[index]->sourceRange);
                    diag << SemanticFacts::getCaseConditionStr(cond);
                }

                for (auto [first, second] : decisionDag->overlappingClauses) {
                    auto& diag = diagnostics->add(rootSymbol, diag::CaseOverlap,
                                                  itemExpressions[second]->sourceRange)
                                 << SemanticFacts::getCaseConditionStr(cond);
                    diag.addNote(diag::NotePreviousUsage, itemExpressions[first]->sourceRange);
                }
            }
        }
    }

    // If the case statement asserts it has full coverage, and our flags allow it,
    // assume full coverage without checking.
    if (options.flags.has(AnalysisFlags::FullCaseUniquePriority) &&
        (stmt.check == UniquePriorityCheck::Unique ||
         stmt.check == UniquePriorityCheck::Priority)) {
        return true;
    }

    // If the case type is not integral then we can never fully satisfy the condition.
    // Non-constant items or constant condition is also not coverable.
    if (!caseType.isIntegral() || hasNonConstItems || stmt.expr.eval(evalContext))
        return false;

    // TODO: handle case inside
    if (stmt.condition == CaseStatementCondition::Inside)
        return false;

    const bool fullCaseFourState = options.flags.has(AnalysisFlags::FullCaseFourState);
    if (stmt.condition == CaseStatementCondition::Normal || !caseType.isFourState()) {
        // The number of non-duplicate elements needs to match the number
        // of possible values for the case expression. This depends on
        // whether the type is 2-state or 4-state.
        if (caseType.isFourState() && fullCaseFourState)
            return bitWidth < 16 && elems.size() >= (size_t)std::pow(4, bitWidth);
        else
            return bitWidth < 32 && elems.size() >= (1ull << bitWidth);
    }

    // If we're checking for four-state wildcard coverage we simply need to
    // find an entry that is all Z bits. This is because Z is always a wildcard,
    // so the only way to specify an entry that hits all Z's will also cover
    // all other bits too.
    if (fullCaseFourState) {
        for (auto& val : intVals) {
            if (val.countLeadingZs() >= bitWidth)
                return true;
        }
        return false;
    }

    // Otherwise do the full wildcard coverage search.
    if (!decisionDag)
        makeDecisionDag();

    return decisionDag->isExhaustive();
}

} // namespace slang::analysis
