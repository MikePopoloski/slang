//! @file NoOldAlwaysCombSyntax.h
//! @brief No old always comb syntax slang-tidy check
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "TidyFactory.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace no_latches_on_design {
struct MainVisitor : public ASTVisitor<MainVisitor, true, false> {
    explicit MainVisitor(Diagnostics& diagnostics) : diags(diagnostics) {}

    Diagnostics& diags;

    void handle(const VariableSymbol& symbol) {
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
    explicit NoLatchesOnDesign(const TidyConfig::CheckConfigs& config, TidyKind kind) :
        TidyCheck(config, kind) {}

    bool check(const RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        if (!diagnostics.empty())
            return false;
        return true;
    }

    DiagCode diagCode() const override { return diag::NoLatchesOnDesign; }

    std::string diagString() const override { return "Latches are not allowed in this design"; }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "NoLatchesOnDesign"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Checks for latches in the design. It will fail if any are found.";
    }
};

REGISTER(NoLatchesOnDesign, NoLatchesOnDesign, TidyKind::Synthesis)
