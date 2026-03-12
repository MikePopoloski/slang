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

namespace {

// A visitor over a for/foreach loop statement that checks for:
//   1. Multiple modifications of loop variables.
//   2. Unmodified condition variables.
//   3. Loop variable capture inside fork-join_any/none blocks.
struct LoopVarsVisitor : public ASTVisitor<LoopVarsVisitor, VisitFlags::AllGood> {
    const Symbol& rootSymbol;
    Diagnostics& diagnostics;

    // Symbols that are advanced by all currently-active loops.
    using StepSymbolMap = flat_hash_map<const ValueSymbol*, SourceRange>;
    StepSymbolMap stepSymbols;

    // Variables used in for loop condition expressions. They get removed when
    // we notice writes to them, so at the end of the loop anything in here
    // represents an unmodified variable.
    SmallSet<const ValueSymbol*, 4> conditionVars;

    // Stack of fork block kinds and the loop-variable snapshots taken at each
    // fork boundary. A variable in the snapshot was active (from an enclosing
    // loop) when the fork was entered; variables added by loops *inside* the
    // fork are not in the snapshot and must not trigger warnings.
    SmallVector<std::pair<StepSymbolMap, StatementBlockKind>> forkStack;

    LoopVarsVisitor(const Symbol& rootSymbol, Diagnostics& diagnostics) :
        rootSymbol(rootSymbol), diagnostics(diagnostics) {}

    void onWriteExpr(const Expression& expr) {
        if (auto sym = getWriteTarget(expr)) {
            conditionVars.erase(sym);
            if (auto it = stepSymbols.find(sym); it != stepSymbols.end()) {
                auto& diag = diagnostics.add(rootSymbol, diag::LoopVarModify, expr.sourceRange);
                diag << sym->name;
                diag.addNote(diag::NoteLoopVarStep, it->second);
            }
        }
    }

    void handle(const NamedValueExpression& expr) {
        if (!forkStack.empty()) {
            auto& [vars, kind] = forkStack.back();
            if (auto it = vars.find(&expr.symbol); it != vars.end()) {
                auto forkStr = kind == StatementBlockKind::JoinNone ? "fork-join_none"sv
                                                                    : "fork-join_any"sv;
                auto& diag = diagnostics.add(rootSymbol, diag::ForkLoopVar, expr.sourceRange);
                diag << expr.symbol.name << forkStr;
                diag.addNote(diag::NoteLoopVarStep, it->second);
            }
        }
        visitDefault(expr);
    }

    void handle(const UnaryExpression& expr) {
        onWriteExpr(expr);
        visitDefault(expr);
    }

    void handle(const AssignmentExpression& expr) {
        onWriteExpr(expr);
        visitDefault(expr);
    }

    void handle(const BlockStatement& block) {
        const bool isForkAnyNone = block.blockKind == StatementBlockKind::JoinAny ||
                                   block.blockKind == StatementBlockKind::JoinNone;
        if (isForkAnyNone)
            forkStack.push_back({stepSymbols, block.blockKind});

        visitDefault(block);

        if (isForkAnyNone)
            forkStack.pop_back();
    }

    void handle(const ForLoopStatement& loop) {
        SmallVector<const ValueSymbol*> condSymbols;
        if (loop.stopExpr) {
            auto condVisitor = makeVisitor([&](auto& vis, const NamedValueExpression& expr) {
                auto& sym = expr.symbol;
                if (VariableSymbol::isKind(sym.kind)) {
                    if (conditionVars.insert(&sym).second)
                        condSymbols.push_back(&sym);
                }
                vis.visitDefault(expr);
            });
            loop.stopExpr->visit(condVisitor);
        }

        // Count the step expressions as writes.
        for (auto step : loop.steps) {
            if (auto target = getWriteTarget(*step)) {
                stepSymbols.emplace(target, step->sourceRange);
                conditionVars.erase(target);
            }
        }

        loop.body.visit(*this);

        // Emit cond-not-modified diagnostics if none of the condition variables
        // were modified inside this loop's body.
        if (!condSymbols.empty()) {
            size_t count = 0;
            for (auto sym : condSymbols)
                count += conditionVars.erase(sym);

            if (count == condSymbols.size())
                diagnostics.add(rootSymbol, diag::LoopCondNotModified, loop.stopExpr->sourceRange);
        }
    }

    void handle(const ForeachLoopStatement& loop) {
        for (auto& dim : loop.loopDims) {
            if (auto var = dim.loopVar)
                stepSymbols.emplace(var, SourceRange{var->location, var->location});
        }

        loop.body.visit(*this);
    }

private:
    static const ValueSymbol* getWriteTarget(const Expression& expr) {
        if (expr.kind == ExpressionKind::UnaryOp) {
            auto& unary = expr.as<UnaryExpression>();
            if (OpInfo::isLValue(unary.op) && unary.operand().kind == ExpressionKind::NamedValue)
                return &unary.operand().as<NamedValueExpression>().symbol;
        }
        else if (expr.kind == ExpressionKind::Assignment) {
            auto& assign = expr.as<AssignmentExpression>();
            if (assign.left().kind == ExpressionKind::NamedValue)
                return &assign.left().as<NamedValueExpression>().symbol;
        }
        return nullptr;
    }
};

} // anonymous namespace

void FlowAnalysisBase::checkLoopVars(const Statement& loopStmt) {
    if (!diagnostics)
        return;

    LoopVarsVisitor visitor(rootSymbol, *diagnostics);
    loopStmt.visit(visitor);
}

} // namespace slang::analysis
