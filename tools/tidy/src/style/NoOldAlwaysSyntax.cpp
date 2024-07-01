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
            // Parent scopes of the always block
            std::set<const Scope*> scopes;
            for (auto scope = symbol.getHierarchicalParent(); scope;
                 scope = scope->asSymbol().getHierarchicalParent()) {
                scopes.insert(scope);
            }

            // If there are assignments of variables that are declared outside the always block,
            // issue the diagnostic
            CollectLHSSymbols visitor;
            symbol.visit(visitor);
            for (auto& s : visitor.symbols)
                if (scopes.contains(s->getHierarchicalParent()))
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
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::NoOldAlwaysSyntax; }

    std::string diagString() const override { return "use of old always verilog syntax"; }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "NoOldAlwaysSyntax"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Checks if old always verilog syntax is being use in the design.";
    }
};

REGISTER(NoOldAlwaysSyntax, NoOldAlwaysSyntax, TidyKind::Style)
