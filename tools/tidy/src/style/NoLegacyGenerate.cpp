// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace no_legacy_generate {

struct GenerateVisitor : public SyntaxVisitor<GenerateVisitor> {
    void handle(const GenerateRegionSyntax& syntax) { foundGenerate.push_back(&syntax); }

public:
    std::vector<const GenerateRegionSyntax*> foundGenerate;
};

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const InstanceBodySymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)
        if (!symbol.getSyntax())
            return;

        GenerateVisitor visitor;
        symbol.getSyntax()->visit(visitor);

        for (const auto& syntax : visitor.foundGenerate) {
            diags.add(diag::NoLegacyGenerate, syntax->keyword.location());
        }
    }
};
} // namespace no_legacy_generate

using namespace no_legacy_generate;
class NoLegacyGenerate : public TidyCheck {
public:
    [[maybe_unused]] explicit NoLegacyGenerate(TidyKind kind) : TidyCheck(kind) {}

    bool check(const ast::RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::NoLegacyGenerate; }
    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }
    std::string diagString() const override { return "usage of generate block is deprecated"; }
    std::string name() const override { return "NoLegacyGenerate"; }
    std::string description() const override { return shortDescription(); }
    std::string shortDescription() const override {
        return "Enforces that no generate block is declared since it is deprecated";
    }
};

REGISTER(NoLegacyGenerate, NoLegacyGenerate, TidyKind::Style)
