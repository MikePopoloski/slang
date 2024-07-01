// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace generate_named {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, false> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const GenerateBlockSymbol& symbol) {

        NEEDS_SKIP_SYMBOL(symbol)

        if (!symbol.getParentScope())
            return;

        auto& parSymbol = symbol.getParentScope()->asSymbol();

        bool isUnnamed = symbol.name.empty();
        if (parSymbol.kind == SymbolKind::GenerateBlockArray) {
            if (symbol.constructIndex != 0)
                return;
            isUnnamed = parSymbol.name.empty();
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
    [[maybe_unused]] explicit GenerateNamed(TidyKind kind) : TidyCheck(kind) {}

    bool check(const ast::RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::GenerateNamed; }
    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }
    std::string diagString() const override { return "definition of an unnamed generate block"; }
    std::string name() const override { return "GenerateNamed"; }
    std::string description() const override { return shortDescription(); }
    std::string shortDescription() const override {
        return "Enforces that each generate block is named";
    }
};

REGISTER(GenerateNamed, GenerateNamed, TidyKind::Style)
