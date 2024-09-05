// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace no_latches_on_design {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, false> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const VariableSymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)

        if (symbol.drivers().empty())
            return;

        auto firstDriver = *symbol.drivers().begin();
        if (firstDriver && firstDriver->isInAlwaysLatchBlock()) {
            diags.add(diag::NoLatchesOnDesign, symbol.location);
        }
    }
};
} // namespace no_latches_on_design

using namespace no_latches_on_design;

class NoLatchesOnDesign : public TidyCheck {
public:
    [[maybe_unused]] explicit NoLatchesOnDesign(TidyKind kind) : TidyCheck(kind) {}

    bool check(const RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::NoLatchesOnDesign; }

    std::string diagString() const override { return "latches are not allowed in this design"; }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Error; }

    std::string name() const override { return "NoLatchesOnDesign"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Checks for latches in the design. It will fail if any are found.";
    }
};

REGISTER(NoLatchesOnDesign, NoLatchesOnDesign, TidyKind::Synthesis)
