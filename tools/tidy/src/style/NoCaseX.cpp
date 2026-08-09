// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

using namespace slang;
using namespace slang::ast;

namespace no_case_x {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, VisitFlags::StatementsCanonical> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const CaseStatement& stmt) {
        NEEDS_SKIP_STATEMENT(stmt)

        if (stmt.condition == CaseStatementCondition::WildcardXOrZ)
            diags.add(diag::NoCaseX, stmt.sourceRange);
        visitDefault(stmt);
    }

    void handle(const PatternCaseStatement& stmt) {
        NEEDS_SKIP_STATEMENT(stmt)

        if (stmt.condition == CaseStatementCondition::WildcardXOrZ)
            diags.add(diag::NoCaseX, stmt.sourceRange);
        visitDefault(stmt);
    }
};
} // namespace no_case_x

using namespace no_case_x;

class NoCaseX : public TidyCheck {
public:
    [[maybe_unused]] explicit NoCaseX(TidyKind kind,
                                      std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::NoCaseX; }

    std::string diagString() const override { return "use of casex not recommended"; }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "NoCaseX"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override { return "Checks for uses of casex."; }
};

REGISTER(NoCaseX, NoCaseX, TidyKind::Style)
