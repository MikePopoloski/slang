// SPDX-FileCopyrightText: Ajeetha Kumari Venkatesan
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

using namespace slang;
using namespace slang::ast;

namespace concurrent_assert_has_fail_action {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, VisitFlags::StatementsCanonical> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const ConcurrentAssertionStatement& stmt) {
        NEEDS_SKIP_STATEMENT(stmt)

        if (stmt.assertionKind == AssertionKind::Assert && stmt.ifFalse == nullptr)
            diags.add(diag::ConcurrentAssertHasFailAction, stmt.sourceRange);
        visitDefault(stmt);
    }
};
} // namespace concurrent_assert_has_fail_action

using namespace concurrent_assert_has_fail_action;

class ConcurrentAssertHasFailAction : public TidyCheck {
public:
    [[maybe_unused]] explicit ConcurrentAssertHasFailAction(
        TidyKind kind, std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::ConcurrentAssertHasFailAction; }

    std::string diagString() const override {
        return "concurrent assertion has no else action block";
    }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "ConcurrentAssertHasFailAction"; }

    std::string description() const override {
        return "Assert statement is missing a fail action block; errors will produce only a "
               "generic simulator message.";
    }

    std::string shortDescription() const override {
        return "Checks that concurrent assert property statements have an else fail action block.";
    }
};

REGISTER(ConcurrentAssertHasFailAction, ConcurrentAssertHasFailAction, TidyKind::Assertion)
