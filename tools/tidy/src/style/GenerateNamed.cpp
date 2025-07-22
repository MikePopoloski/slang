// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace generate_named {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, false, false, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const GenerateBlockSymbol& symbol) {

        NEEDS_SKIP_SYMBOL(symbol)

        if (!symbol.getParentScope())
            return;

        auto& parSymbol = symbol.getParentScope()->asSymbol();

        bool isUnnamed = symbol.isUnnamed;
        if (auto array = parSymbol.as_if<GenerateBlockArraySymbol>()) {
            if (symbol.constructIndex != 0)
                return;
            isUnnamed = array->isUnnamed;
        }

        if (isUnnamed) {
            diags.add(diag::GenerateNamed, symbol.location);
        }
    }
};
} // namespace generate_named

using namespace generate_named;
class GenerateNamed : public TidyCheck {
public:
    [[maybe_unused]] explicit GenerateNamed(TidyKind kind,
                                            std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const ast::RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::GenerateNamed; }
    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }
    std::string diagString() const override { return "definition of an unnamed generate block"; }
    std::string name() const override { return "GenerateNamed"; }
    std::string description() const override { return shortDescription(); }
    std::string shortDescription() const override {
        return "Enforces that each generate block is named";
    }
};

REGISTER(GenerateNamed, GenerateNamed, TidyKind::Style)
