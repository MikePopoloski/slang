// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

#include "slang/syntax/AllSyntax.h"

using namespace slang;
using namespace slang::ast;

namespace no_ansi_port_decl {
struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, false> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const PortSymbol& port) {
        NEEDS_SKIP_SYMBOL(port)

        if (!port.isAnsiPort) {
            diags.add(diag::OnlyANSIPortDecl, port.location) << port.internalSymbol->name;
        }
    }
};
} // namespace no_ansi_port_decl

using namespace no_ansi_port_decl;
class OnlyANSIPortDecl : public TidyCheck {
public:
    [[maybe_unused]] explicit OnlyANSIPortDecl(TidyKind kind) : TidyCheck(kind) {}

    bool check(const ast::RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::OnlyANSIPortDecl; }
    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }
    std::string diagString() const override {
        return "port '{}' is declared using non-ANSI port declaration style";
    }
    std::string name() const override { return "OnlyANSIPortDecl"; }
    std::string description() const override {
        return "Enforces that all ports in the design are declared using the ANSI port "
               "declaration style";
    }
    std::string shortDescription() const override { return "Enforces ANSI port declaration style"; }
};

REGISTER(OnlyANSIPortDecl, OnlyANSIPortDecl, TidyKind::Style)
