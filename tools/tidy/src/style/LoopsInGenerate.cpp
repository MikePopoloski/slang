// SPDX-License-Identifier: MIT
// 18-341 Custom Rule

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace loops_in_generate {

struct LoopVisitor : public SyntaxVisitor<LoopVisitor> {
    void handle(const ForLoopStatementSyntax& syntax) { foundForLoops.push_back(&syntax); }

    void handle(const LoopGenerateSyntax& syntax) { foundGenerateLoops.push_back(&syntax); }

public:
    std::vector<const ForLoopStatementSyntax*> foundForLoops;
    std::vector<const LoopGenerateSyntax*> foundGenerateLoops;
};

bool isInsideGenerate(const SyntaxNode* node) {
    while (node) {
        if (node->kind == SyntaxKind::GenerateRegion || node->kind == SyntaxKind::GenerateBlock) {
            return true;
        }
        node = node->parent;
    }
    return false;
}

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true, false, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const InstanceBodySymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)
        if (!symbol.getSyntax())
            return;

        LoopVisitor visitor;
        symbol.getSyntax()->visit(visitor);

        for (const auto& loop : visitor.foundForLoops) {
            if (!isInsideGenerate(loop)) {
                diags.add(diag::LoopsInGenerate, loop->forKeyword.location());
            }
        }

        for (const auto& genLoop : visitor.foundGenerateLoops) {
            if (!isInsideGenerate(genLoop)) {
                diags.add(diag::LoopsInGenerate, genLoop->keyword.location());
            }
        }
    }
};
} // namespace loops_in_generate

using namespace loops_in_generate;
class LoopsInGenerate : public TidyCheck {
public:
    [[maybe_unused]] explicit LoopsInGenerate(TidyKind kind,
                                              std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const ast::RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::LoopsInGenerate; }
    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Error; }
    std::string diagString() const override {
        return "loop statements must be inside generate blocks";
    }
    std::string name() const override { return "LoopsInGenerate"; }
    std::string description() const override { return shortDescription(); }
    std::string shortDescription() const override {
        return "Ensures that all loop statements are enclosed within generate and endgenerate "
               "blocks.";
    }
};

REGISTER(LoopsInGenerate, LoopsInGenerate, TidyKind::Style)
