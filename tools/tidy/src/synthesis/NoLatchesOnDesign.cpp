// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/analysis/AnalysisManager.h"
#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::analysis;

namespace no_latches_on_design {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, false, false, true> {
    const AnalysisManager& analysisManager;

    MainVisitor(Diagnostics& diagnostics, const AnalysisManager& analysisManager) :
        TidyVisitor(diagnostics), analysisManager(analysisManager) {}

    void handle(const VariableSymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)

        auto drivers = analysisManager.getDrivers(symbol);
        if (drivers.empty())
            return;

        auto firstDriver = drivers[0].first;
        if (firstDriver && firstDriver->source == DriverSource::AlwaysLatch) {
            diags.add(diag::NoLatchesOnDesign, symbol.location);
        }
    }
};
} // namespace no_latches_on_design

using namespace no_latches_on_design;

class NoLatchesOnDesign : public TidyCheck {
public:
    [[maybe_unused]] explicit NoLatchesOnDesign(TidyKind kind,
                                                std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const AnalysisManager& analysisManager) override {
        MainVisitor visitor(diagnostics, analysisManager);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::NoLatchesOnDesign; }

    std::string diagString() const override { return "latches are not allowed in this design"; }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Error; }

    std::string name() const override { return "NoLatchesOnDesign"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Checks for latches in the design. It will fail if any are found.";
    }
};

REGISTER(NoLatchesOnDesign, NoLatchesOnDesign, TidyKind::Synthesis)
