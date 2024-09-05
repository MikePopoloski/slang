// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include "fmt/color.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace always_comb_non_blocking {

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, false> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const ProceduralBlockSymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)
        if (symbol.procedureKind == ProceduralBlockKind::AlwaysComb) {
            bool hasNonBlockingAssignment = false;
            symbol.visitStmts(makeVisitor([&](auto&, const AssignmentExpression& expr) {
                if (expr.isNonBlocking()) {
                    hasNonBlockingAssignment = true;
                }
            }));
            if (hasNonBlockingAssignment) {
                diags.add(diag::AlwaysCombNonBlocking, symbol.location);
            }
        }
    }
};
} // namespace always_comb_non_blocking

using namespace always_comb_non_blocking;
class AlwaysCombNonBlocking : public TidyCheck {
public:
    [[maybe_unused]] explicit AlwaysCombNonBlocking(TidyKind kind) : TidyCheck(kind) {}

    bool check(const ast::RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::AlwaysCombNonBlocking; }
    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }
    std::string diagString() const override {
        return "use of a non blocking assignment inside always_comb";
    }
    std::string name() const override { return "AlwaysCombNonBlocking"; }
    std::string description() const override { return shortDescription(); }
    std::string shortDescription() const override {
        return "Enforces that non blocking assignments are not being used inside always_comb "
               "blocks";
    }
};

REGISTER(AlwaysCombNonBlocking, AlwaysCombNonBlocking, TidyKind::Style)
