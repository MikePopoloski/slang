//------------------------------------------------------------------------------
// AnalyzedAssertion.cpp
// Analysis support for concurrent assertions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/analysis/AnalyzedAssertion.h"

#include "slang/analysis/AnalysisManager.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/diagnostics/AnalysisDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::analysis {

using namespace ast;

static bool isSameClock(const TimingControl& left, const TimingControl& right) {
    if ((left.kind != TimingControlKind::SignalEvent &&
         left.kind != TimingControlKind::EventList) ||
        (right.kind != TimingControlKind::SignalEvent &&
         right.kind != TimingControlKind::EventList)) {
        // Ignore anything invalid here, we only want to compare valid clocks.
        return true;
    }

    if (left.kind != right.kind)
        return false;

    if (left.kind == TimingControlKind::EventList) {
        auto& le = left.as<EventListControl>();
        auto& re = right.as<EventListControl>();
        if (le.events.size() != re.events.size())
            return false;

        for (size_t i = 0; i < le.events.size(); i++) {
            if (!isSameClock(*le.events[i], *re.events[i]))
                return false;
        }
        return true;
    }

    auto& le = left.as<SignalEventControl>();
    auto& re = right.as<SignalEventControl>();
    if (le.edge != re.edge || bool(le.iffCondition) != bool(re.iffCondition))
        return false;

    if (le.iffCondition) {
        if (!le.iffCondition->syntax || !re.iffCondition->syntax)
            return false;
        return le.iffCondition->syntax->isEquivalentTo(*re.iffCondition->syntax);
    }

    if (!le.expr.syntax || !re.expr.syntax)
        return false;

    return le.expr.syntax->isEquivalentTo(*re.expr.syntax);
}

// This visitor implements clock flow and resolution for assertion expressions.
// The requirements for this are scattered around the LRM. Some important parts are:
// - 16.13 describes multiclocked sequences and properties
// - 16.13.3 describes clock flow
// - 16.16.1 describes rules for determining semantic leading clocks
// - F.5.1 describes formal rewrite rules for clocks
struct ClockVisitor {
    using Clock = const TimingControl*;
    using ClockSet = SmallVector<Clock, 2>;

    struct VisitResult {
        ClockSet clocks;
        bool isMulticlockedSeq = false;

        VisitResult() = default;
        VisitResult(Clock clock, bool isMulticlockedSeq) :
            clocks{clock}, isMulticlockedSeq(isMulticlockedSeq) {}

        static VisitResult unionWith(const VisitResult& left, const VisitResult& right) {
            VisitResult result;
            result.clocks.reserve(left.clocks.size() + right.clocks.size());
            result.clocks.append_range(left.clocks);
            result.clocks.append_range(right.clocks);
            return result;
        }
    };

    AnalysisContext& context;
    const Symbol& parentSymbol;
    SmallVector<const AssertionExpr*> expansionStack;
    bool bad = false;

    ClockVisitor(AnalysisContext& context, const Symbol& parentSymbol) :
        context(context), parentSymbol(parentSymbol) {}

    VisitResult visit(const InvalidAssertionExpr&, Clock, bool) {
        bad = true;
        return {};
    }

    VisitResult visit(const SimpleAssertionExpr& expr, Clock outerClock, bool requireSeq) {
        if (expr.expr.kind == ExpressionKind::AssertionInstance) {
            auto& aie = expr.expr.as<AssertionInstanceExpression>();
            if (aie.isRecursiveProperty)
                return {};

            SLANG_ASSERT(expr.syntax);
            expansionStack.push_back(&expr);
            auto result = aie.body.visit(*this, outerClock,
                                         requireSeq || aie.type->isSequenceType());
            expansionStack.pop_back();
            return result;
        }

        return inheritedClock(expr, outerClock, true);
    }

    VisitResult visit(const SequenceConcatExpr& expr, Clock outerClock, bool) {
        Clock firstClock = nullptr;
        const AssertionExpr* lastExpr = nullptr;
        bool lastWasMulticlocked = false;
        bool isMulticlockedSeq = false;

        for (auto& elem : expr.elements) {
            auto result = elem.sequence->visit(*this, outerClock, true);
            if (!result.clocks.empty()) {
                if (!firstClock) {
                    firstClock = result.clocks[0];
                }
                else if (result.isMulticlockedSeq || !isSameClock(*firstClock, *result.clocks[0])) {
                    // When concatenating differently clocked sequences, the maximal single-clocked
                    // subsequences must not admit an empty match.
                    if (!lastWasMulticlocked)
                        requireOnlyNonEmptyMatch(*lastExpr);
                    if (!result.isMulticlockedSeq)
                        requireOnlyNonEmptyMatch(*elem.sequence);

                    isMulticlockedSeq = true;
                    if (elem.delay.min > 1 || elem.delay.max != elem.delay.min)
                        badMulticlockedSeq(*elem.sequence, *lastExpr, elem.delayRange);
                }
            }
            lastExpr = elem.sequence;
            lastWasMulticlocked = result.isMulticlockedSeq;
        }

        if (!firstClock)
            return {};

        return {firstClock, isMulticlockedSeq};
    }

    VisitResult visit(const SequenceWithMatchExpr& expr, Clock outerClock, bool) {
        return expr.expr.visit(*this, outerClock, true);
    }

    VisitResult visit(const FirstMatchAssertionExpr& expr, Clock outerClock, bool) {
        return expr.seq.visit(*this, outerClock, true);
    }

    VisitResult visit(const StrongWeakAssertionExpr& expr, Clock outerClock, bool) {
        return expr.expr.visit(*this, outerClock, true);
    }

    VisitResult visit(const ClockingAssertionExpr& expr, Clock, bool requireSeq) {
        // Outer clock is ignored here.
        return expr.expr.visit(*this, &expr.clocking, requireSeq);
    }

    VisitResult visit(const UnaryAssertionExpr& expr, Clock outerClock, bool) {
        auto result = expr.expr.visit(*this, outerClock, false);
        if (expr.op == UnaryAssertionOperator::Not)
            return result;
        return inheritedClock(expr, outerClock, false);
    }

    VisitResult visit(const AbortAssertionExpr& expr, Clock outerClock, bool) {
        auto result = expr.expr.visit(*this, outerClock, false);
        if (!expr.isSync)
            return result;
        return inheritedClock(expr, outerClock, false);
    }

    VisitResult visit(const BinaryAssertionExpr& expr, Clock outerClock, bool requireSeq) {
        auto checkBadSeq = [&](const VisitResult& lresult, const VisitResult& rresult) {
            if (lresult.isMulticlockedSeq || rresult.isMulticlockedSeq ||
                (!lresult.clocks.empty() && !rresult.clocks.empty() &&
                 !isSameClock(*lresult.clocks[0], *rresult.clocks[0]))) {
                badMulticlockedSeq(expr.left, expr.right, expr.opRange);
            }
        };

        switch (expr.op) {
            case BinaryAssertionOperator::Intersect:
            case BinaryAssertionOperator::Throughout:
            case BinaryAssertionOperator::Within: {
                auto lresult = expr.left.visit(*this, outerClock, true);
                auto rresult = expr.right.visit(*this, outerClock, true);
                checkBadSeq(lresult, rresult);
                return lresult;
            }
            case BinaryAssertionOperator::Until:
            case BinaryAssertionOperator::SUntil:
            case BinaryAssertionOperator::UntilWith:
            case BinaryAssertionOperator::SUntilWith:
                expr.left.visit(*this, outerClock, false);
                expr.right.visit(*this, outerClock, false);
                return inheritedClock(expr, outerClock, false);
            case BinaryAssertionOperator::And:
            case BinaryAssertionOperator::Or: {
                // Clocks come from both sides.
                auto lresult = expr.left.visit(*this, outerClock, requireSeq);
                auto rresult = expr.right.visit(*this, outerClock, requireSeq);
                if (requireSeq)
                    checkBadSeq(lresult, rresult);
                return VisitResult::unionWith(lresult, rresult);
            }
            case BinaryAssertionOperator::Iff:
            case BinaryAssertionOperator::Implies: {
                // Clocks come from both sides.
                auto lresult = expr.left.visit(*this, outerClock, false);
                auto rresult = expr.right.visit(*this, outerClock, false);
                return VisitResult::unionWith(lresult, rresult);
            }
            case BinaryAssertionOperator::OverlappedImplication:
            case BinaryAssertionOperator::NonOverlappedImplication:
            case BinaryAssertionOperator::OverlappedFollowedBy:
            case BinaryAssertionOperator::NonOverlappedFollowedBy: {
                // Clocks come from just the left hand side.
                auto lresult = expr.left.visit(*this, outerClock, true);
                expr.right.visit(*this, outerClock, false);
                return lresult;
            }
            default:
                SLANG_UNREACHABLE;
        }
    }

    VisitResult visit(const ConditionalAssertionExpr& expr, Clock outerClock, bool) {
        expr.ifExpr.visit(*this, outerClock, false);
        if (expr.elseExpr)
            expr.elseExpr->visit(*this, outerClock, false);

        // Semantic leading clock is always inherited.
        return inheritedClock(expr, outerClock, false);
    }

    VisitResult visit(const CaseAssertionExpr& expr, Clock outerClock, bool) {
        for (auto& item : expr.items)
            item.body->visit(*this, outerClock, false);

        if (expr.defaultCase)
            expr.defaultCase->visit(*this, outerClock, false);

        // Semantic leading clock is always inherited.
        return inheritedClock(expr, outerClock, false);
    }

    VisitResult visit(const DisableIffAssertionExpr& expr, Clock outerClock, bool) {
        return expr.expr.visit(*this, outerClock, false);
    }

private:
    VisitResult inheritedClock(const AssertionExpr& expr, Clock outerClock, bool requireSeq) {
        if (!outerClock) {
            if (!bad) {
                bad = true;

                SourceRange range;
                SLANG_ASSERT(expr.syntax);
                if (!expansionStack.empty())
                    range = expansionStack.front()->syntax->sourceRange();
                else
                    range = expr.syntax->sourceRange();

                auto& diag = context.addDiag(parentSymbol, diag::AssertionNoClock, range);
                diag << (requireSeq ? "sequence"sv : "property"sv);

                if (!expansionStack.empty()) {
                    for (size_t i = 1; i < expansionStack.size(); i++) {
                        diag.addNote(diag::NoteRequiredHere,
                                     expansionStack[i]->syntax->sourceRange());
                    }
                    diag.addNote(diag::NoteRequiredHere, expr.syntax->sourceRange());
                }
            }
            return {};
        }
        return {outerClock, false};
    }

    void badMulticlockedSeq(const AssertionExpr& left, const AssertionExpr& right,
                            SourceRange opRange) {
        if (!bad) {
            bad = true;

            SLANG_ASSERT(left.syntax);
            SLANG_ASSERT(right.syntax);

            auto leftRange = left.syntax->sourceRange();
            auto range = opRange;
            if (!range.start())
                range = leftRange;

            context.addDiag(parentSymbol, diag::InvalidMulticlockedSeqOp, range)
                << leftRange << right.syntax->sourceRange();
        }
    }

    void requireOnlyNonEmptyMatch(const AssertionExpr& expr) {
        if (!bad && expr.checkNondegeneracy().status.has(NondegeneracyStatus::AdmitsEmpty)) {
            bad = true;

            SLANG_ASSERT(expr.syntax);
            context.addDiag(parentSymbol, diag::MulticlockedSeqEmptyMatch,
                            expr.syntax->sourceRange());
        }
    }
};

AnalyzedAssertion::AnalyzedAssertion(AnalysisContext& context, const TimingControl* contextualClock,
                                     const Symbol& parentSymbol,
                                     const ConcurrentAssertionStatement& stmt) :
    analyzedStatement(&stmt) {

    ClockVisitor visitor(context, parentSymbol);
    stmt.propertySpec.visit(visitor, contextualClock, false);
}

} // namespace slang::analysis
