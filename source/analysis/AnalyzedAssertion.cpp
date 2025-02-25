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

namespace slang::analysis {

using namespace ast;

// This visitor implements clock flow and resolution for assertion expressions.
// The requirements for this are scattered around the LRM. Some important parts are:
// - 16.13 describes multiclocked sequences and properties
// - 16.13.3 describes clock flow
// - 16.16.1 describes rules for determining semantic leading clocks
// - F.5.1 describes formal rewrite rules for clocks
struct ClockVisitor {
    using Clock = const TimingControl*;
    using ClockSet = SmallVector<Clock, 2>;

    AnalysisContext& context;
    const Symbol& parentSymbol;
    SmallVector<const AssertionExpr*> expansionStack;
    bool bad = false;

    ClockVisitor(AnalysisContext& context, const Symbol& parentSymbol) :
        context(context), parentSymbol(parentSymbol) {}

    ClockSet visit(const InvalidAssertionExpr&, Clock, bool) {
        bad = true;
        return {};
    }

    ClockSet visit(const SimpleAssertionExpr& expr, Clock outerClock, bool requireSeq) {
        if (expr.expr.kind == ExpressionKind::AssertionInstance) {
            auto& aie = expr.expr.as<AssertionInstanceExpression>();
            if (aie.isRecursiveProperty)
                return {};

            SLANG_ASSERT(expr.syntax);
            expansionStack.push_back(&expr);
            auto clocks = aie.body.visit(*this, outerClock,
                                         requireSeq || aie.type->isSequenceType());
            expansionStack.pop_back();
            return clocks;
        }

        return inheritedClock(expr, outerClock, true);
    }

    ClockSet visit(const SequenceConcatExpr& expr, Clock outerClock, bool) {
        Clock firstClock = nullptr;
        for (auto& elem : expr.elements) {
            auto clocks = elem.sequence->visit(*this, outerClock, true);
            if (!firstClock && !clocks.empty())
                firstClock = clocks[0];
        }
        return {firstClock};
    }

    ClockSet visit(const SequenceWithMatchExpr& expr, Clock outerClock, bool) {
        return expr.expr.visit(*this, outerClock, true);
    }

    ClockSet visit(const FirstMatchAssertionExpr& expr, Clock outerClock, bool) {
        return expr.seq.visit(*this, outerClock, true);
    }

    ClockSet visit(const StrongWeakAssertionExpr& expr, Clock outerClock, bool) {
        return expr.expr.visit(*this, outerClock, true);
    }

    ClockSet visit(const ClockingAssertionExpr& expr, Clock, bool requireSeq) {
        // Outer clock is ignored here.
        return expr.expr.visit(*this, &expr.clocking, requireSeq);
    }

    ClockSet visit(const UnaryAssertionExpr& expr, Clock outerClock, bool) {
        auto clocks = expr.expr.visit(*this, outerClock, false);
        if (expr.op == UnaryAssertionOperator::Not)
            return clocks;
        return inheritedClock(expr, outerClock, false);
    }

    ClockSet visit(const AbortAssertionExpr& expr, Clock outerClock, bool) {
        auto clocks = expr.expr.visit(*this, outerClock, false);
        if (!expr.isSync)
            return clocks;
        return inheritedClock(expr, outerClock, false);
    }

    ClockSet visit(const BinaryAssertionExpr& expr, Clock outerClock, bool requireSeq) {
        switch (expr.op) {
            case BinaryAssertionOperator::Intersect:
            case BinaryAssertionOperator::Throughout:
            case BinaryAssertionOperator::Within: {
                // TODO: Clocks must be the same.
                auto lclocks = expr.left.visit(*this, outerClock, true);
                auto rclocks = expr.right.visit(*this, outerClock, true);
                return lclocks;
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
                auto lclocks = expr.left.visit(*this, outerClock, requireSeq);
                auto rclocks = expr.right.visit(*this, outerClock, requireSeq);
                lclocks.append_range(rclocks);
                return lclocks;
            }
            case BinaryAssertionOperator::Iff:
            case BinaryAssertionOperator::Implies: {
                // Clocks come from both sides.
                auto lclocks = expr.left.visit(*this, outerClock, false);
                auto rclocks = expr.right.visit(*this, outerClock, false);
                lclocks.append_range(rclocks);
                return lclocks;
            }
            case BinaryAssertionOperator::OverlappedImplication:
            case BinaryAssertionOperator::NonOverlappedImplication:
            case BinaryAssertionOperator::OverlappedFollowedBy:
            case BinaryAssertionOperator::NonOverlappedFollowedBy: {
                // Clocks come from just the left hand side.
                auto lclocks = expr.left.visit(*this, outerClock, true);
                expr.right.visit(*this, outerClock, false);
                return lclocks;
            }
            default:
                SLANG_UNREACHABLE;
        }
    }

    ClockSet visit(const ConditionalAssertionExpr& expr, Clock outerClock, bool) {
        expr.ifExpr.visit(*this, outerClock, false);
        if (expr.elseExpr)
            expr.elseExpr->visit(*this, outerClock, false);

        // Semantic leading clock is always inherited.
        return inheritedClock(expr, outerClock, false);
    }

    ClockSet visit(const CaseAssertionExpr& expr, Clock outerClock, bool) {
        for (auto& item : expr.items)
            item.body->visit(*this, outerClock, false);

        if (expr.defaultCase)
            expr.defaultCase->visit(*this, outerClock, false);

        // Semantic leading clock is always inherited.
        return inheritedClock(expr, outerClock, false);
    }

    ClockSet visit(const DisableIffAssertionExpr& expr, Clock outerClock, bool) {
        return expr.visit(*this, outerClock, false);
    }

private:
    ClockSet inheritedClock(const AssertionExpr& expr, Clock outerClock, bool requireSeq) {
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
        return {outerClock};
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
