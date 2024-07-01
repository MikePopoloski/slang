// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace no_dot_start_in_port_connection {

struct PortConnectionVisitor : public SyntaxVisitor<PortConnectionVisitor> {
    void handle(const WildcardPortConnectionSyntax& port) { foundPorts.push_back(&port); }

public:
    std::vector<const WildcardPortConnectionSyntax*> foundPorts;
};

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const InstanceBodySymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)
        PortConnectionVisitor visitor;
        symbol.getSyntax()->visit(visitor);
        for (const auto port : visitor.foundPorts)
            diags.add(diag::NoDotStarInPortConnection, port->star.location());
    }
};
} // namespace no_dot_start_in_port_connection

using namespace no_dot_start_in_port_connection;

class NoDotStarInPortConnection : public TidyCheck {
public:
    [[maybe_unused]] explicit NoDotStarInPortConnection(TidyKind kind) : TidyCheck(kind) {}

    bool check(const RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::NoDotStarInPortConnection; }

    std::string diagString() const override { return "use of .* in port connection list"; }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "NoDotStarInPortConnection"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Checks if in a module instantiation any port is connected using .* syntax.";
    }
};

REGISTER(NoDotStarInPortConnection, NoDotStarInPortConnection, TidyKind::Style)
