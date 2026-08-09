// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

using namespace slang;
using namespace slang::ast;

namespace no_def_param {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, VisitFlags::Symbols> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const DefParamSymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)

        diags.add(diag::NoDefParam, symbol.location);
    }
};
} // namespace no_def_param

using namespace no_def_param;

class NoDefParam : public TidyCheck {
public:
    [[maybe_unused]] explicit NoDefParam(TidyKind kind,
                                         std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::NoDefParam; }

    std::string diagString() const override { return "use of defparam not recommended"; }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "NoDefParam"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override { return "Checks for any use of defparam."; }
};

REGISTER(NoDefParam, NoDefParam, TidyKind::Style)
