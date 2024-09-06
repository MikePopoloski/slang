// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"
#include <iostream>

#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::syntax;

namespace no_implicit_port_name_in_port_connection {

struct PortConnectionVisitor : public SyntaxVisitor<PortConnectionVisitor> {
    void handle(const PortConnectionSyntax& syntax) {
        if (syntax.toString().find('(') == std::string::npos)
            found = true;
    }

public:
    bool found{false};
};

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const InstanceBodySymbol& symbol) {
        NEEDS_SKIP_SYMBOL(symbol)
        PortConnectionVisitor visitor;
        symbol.getSyntax()->visit(visitor);
        if (visitor.found)
            diags.add(diag::NoImplicitPortNameInPortConnection, symbol.location);
    }
};
} // namespace no_implicit_port_name_in_port_connection

using namespace no_implicit_port_name_in_port_connection;

class NoImplicitPortNameInPortConnection : public TidyCheck {
public:
    [[maybe_unused]] explicit NoImplicitPortNameInPortConnection(TidyKind kind) : TidyCheck(kind) {}

    bool check(const RootSymbol& root) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::NoImplicitPortNameInPortConnection; }

    std::string diagString() const override {
        return "port name not specified. Please use .port_name(net) syntax.";
    }

    DiagnosticSeverity diagSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "NoImplicitPortNameInPortConnection"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Checks if in a module instantiation any port is connected using .port_name syntax.";
    }
};

REGISTER(NoImplicitPortNameInPortConnection, NoImplicitPortNameInPortConnection, TidyKind::Style)
