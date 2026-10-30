// SPDX-FileCopyrightText: Ajeetha Kumari Venkatesan
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

using namespace slang;
using namespace slang::ast;

namespace conditional_operator_precedence {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, VisitFlags::AllCanonical> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const ExpressionConstraint& c) {
        if (skip(sourceManager->getFileName(c.expr.sourceRange.start())))
            return;

        // Violation: top-level constraint expr is a conditional (?:) whose
        // condition is a comparison (==, !=, <, ...). SV precedence parses
        //   lhs == expr ? a : b   as   (lhs == expr) ? a : b
        // rather than the likely intent   lhs == (expr ? a : b).
        if (c.expr.kind != ExpressionKind::ConditionalOp)
            return;

        auto& condExpr = c.expr.as<ConditionalExpression>();
        if (condExpr.conditions.size() != 1 || condExpr.conditions[0].pattern)
            return;

        auto binOp = condExpr.conditions[0].expr->as_if<BinaryExpression>();
        if (!binOp || binOp->isParenthesized() || !OpInfo::isComparison(binOp->op))
            return;

        // Boolean branches are an intended conditional constraint:
        //   mode == 1 ? len < 10 : len > 20
        auto isBoolean = [](const Expression& expr) {
            return expr.type->isIntegral() && expr.type->getBitWidth() == 1;
        };
        if (isBoolean(condExpr.left()) && isBoolean(condExpr.right()))
            return;

        diags.add(diag::ConditionalOperatorPrecedence, c.expr.sourceRange);
    }
};
} // namespace conditional_operator_precedence

using namespace conditional_operator_precedence;

class ConditionalOperatorPrecedence : public TidyCheck {
public:
    [[maybe_unused]] explicit ConditionalOperatorPrecedence(
        TidyKind kind, std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::ConditionalOperatorPrecedence; }

    std::string diagString() const override {
        return "mixed operator precedence in constraint expression; use parentheses around the "
               "conditional expression";
    }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "ConditionalOperatorPrecedence"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Checks for mixed comparison and conditional operator precedence in constraints.";
    }
};

REGISTER(ConditionalOperatorPrecedence, ConditionalOperatorPrecedence, TidyKind::Constraint)
