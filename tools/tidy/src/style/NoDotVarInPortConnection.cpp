// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace no_dot_var_in_port_connection {

struct PortConnectionVisitor : SyntaxVisitor<PortConnectionVisitor> {
    void handle(const NamedPortConnectionSyntax& port) {
        if (!port.openParen)
            foundPorts.push_back(&port);
    }

    std::vector<const NamedPortConnectionSyntax*> foundPorts;
};

struct MainVisitor : TidyVisitor, ASTVisitor<MainVisitor, true, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const InstanceBodySymbol& symbol) const {
        NEEDS_SKIP_SYMBOL(symbol)
        if (!symbol.getSyntax())
            return;

        PortConnectionVisitor visitor;
        symbol.getSyntax()->visit(visitor);

        for (const auto port : visitor.foundPorts)
            diags.add(diag::NoDotVarInPortConnection, port->name.location())
                << port->toString() << port->toString() << port->name.valueText();
    }
};
} // namespace no_dot_var_in_port_connection

using namespace no_dot_var_in_port_connection;

class NoDotVarInPortConnection final : public TidyCheck {
public:
    [[maybe_unused]] explicit NoDotVarInPortConnection(const TidyKind kind) : TidyCheck(kind) {}

    bool check(const RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::NoDotVarInPortConnection; }

    std::string diagString() const override {
        return "use of '{}' in port connection list, consider using '{}({})' instead";
    }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "NoDotVarInPortConnection"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Checks if in a module instantiation any port is connected using .var syntax.";
    }
};

REGISTER(NoDotVarInPortConnection, NoDotVarInPortConnection, TidyKind::Style)
