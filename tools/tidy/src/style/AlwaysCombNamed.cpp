// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace always_comb_named {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, false> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const ProceduralBlockSymbol& symbol) {

        NEEDS_SKIP_SYMBOL(symbol)

        if (symbol.procedureKind != ProceduralBlockKind::AlwaysComb ||
            symbol.getBody().kind != StatementKind::Block)
            return;

        bool isUnnamed = (symbol.getBody().as<ast::BlockStatement>().blockSymbol == nullptr ||
                          symbol.getBody().as<ast::BlockStatement>().blockSymbol->name.empty());

        if (isUnnamed) {
            diags.add(diag::AlwaysCombBlockNamed, symbol.location);
        }
    }
};
} // namespace always_comb_named

using namespace always_comb_named;
class AlwaysCombBlockNamed : public TidyCheck {
public:
    [[maybe_unused]] explicit AlwaysCombBlockNamed(TidyKind kind) : TidyCheck(kind) {}

    bool check(const ast::RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::AlwaysCombBlockNamed; }
    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }
    std::string diagString() const override { return "definition of an unnamed always_comb block"; }
    std::string name() const override { return "AlwaysCombBlockNamed"; }
    std::string description() const override { return shortDescription(); }
    std::string shortDescription() const override {
        return "Enforces that each always_comb block is named";
    }
};

REGISTER(AlwaysCombBlockNamed, AlwaysCombBlockNamed, TidyKind::Style)
