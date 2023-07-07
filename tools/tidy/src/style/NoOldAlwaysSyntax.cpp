// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace no_old_always_syntax {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const ast::ProceduralBlockSymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)

        if (symbol.isFromAssertion)
            return;

        if (symbol.procedureKind == ProceduralBlockKind::Always) {
            diags.add(diag::NoOldAlwaysSyntax, symbol.location);
        }
    }
};
} // namespace no_old_always_syntax

using namespace no_old_always_syntax;

class NoOldAlwaysSyntax : public TidyCheck {
public:
    [[maybe_unused]] explicit NoOldAlwaysSyntax(TidyKind kind) : TidyCheck(kind) {}

    bool check(const RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        if (!diagnostics.empty())
            return false;
        return true;
    }

    DiagCode diagCode() const override { return diag::NoOldAlwaysSyntax; }

    std::string diagString() const override { return "Use of old always verilog syntax"; }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "NoOldAlwaysSyntax "; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Checks if old always verilog syntax is being use in the design.";
    }
};

REGISTER(NoOldAlwaysSyntax, NoOldAlwaysSyntax, TidyKind::Style)
