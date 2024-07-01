// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace always_ff_blocking {

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, false> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const ProceduralBlockSymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)
        if (symbol.procedureKind == ProceduralBlockKind::AlwaysFF) {
            // Collect all declared local variables
            std::vector<std::string_view> locals;
            symbol.visitStmts(makeVisitor([&](auto&, const VariableDeclStatement& decl) {
                locals.push_back(decl.symbol.name);
            }));

            bool hasBlockingAssignments = false;
            symbol.visitStmts(makeVisitor([&](auto&, const AssignmentExpression& expr) {
                if (expr.isBlocking()) {
                    auto identifier = getIdentifier(expr.left());
                    if (identifier && std::find(locals.begin(), locals.end(), identifier.value()) ==
                                          locals.end()) {
                        hasBlockingAssignments = true;
                    }
                }
            }));

            if (hasBlockingAssignments) {
                diags.add(diag::AlwaysFFBlocking, symbol.location);
            }
        }
    }
};
} // namespace always_ff_blocking

using namespace always_ff_blocking;
class AlwaysFFBlocking : public TidyCheck {
public:
    [[maybe_unused]] explicit AlwaysFFBlocking(TidyKind kind) : TidyCheck(kind) {}

    bool check(const ast::RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::AlwaysFFBlocking; }
    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }
    std::string diagString() const override {
        return "use of a blocking assignment for a non local variables inside always_ff";
    }
    std::string name() const override { return "AlwaysFFBlocking"; }
    std::string description() const override { return shortDescription(); }
    std::string shortDescription() const override {
        return "Enforces that blocking assignments are not being used inside always_ff "
               "for non local variables";
    }
};

REGISTER(AlwaysFFBlocking, AlwaysFFBlocking, TidyKind::Style)
