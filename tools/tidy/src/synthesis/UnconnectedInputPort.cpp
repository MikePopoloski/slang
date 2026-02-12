// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "ASTHelperVisitors.h"
#include "TidyDiags.h"

#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/PortSymbols.h"

using namespace slang;
using namespace slang::ast;

namespace unconnected_input_port {

struct MainVisitor : public TidyVisitor, ASTVisitor<MainVisitor, true, false, false, true> {
    explicit MainVisitor(Diagnostics& diagnostics) : TidyVisitor(diagnostics) {}

    void handle(const InstanceSymbol& parentInstance) {
        NEEDS_SKIP_SYMBOL(parentInstance)

        if (!parentInstance.isModule())
            return;

        // Iterate through child instances within this parent module
        for (auto& member : parentInstance.body.members()) {
            if (member.kind != SymbolKind::Instance)
                continue;

            const auto& childInstance = member.as<InstanceSymbol>();

            // Get all ports from the module definition
            auto ports = childInstance.body.getPortList();
            
            // Build a set of all port names
            SmallMap<std::string_view, const PortSymbol*, 8> inputPorts;
            for (const auto* portBase : ports) {
                if (portBase->kind != SymbolKind::Port)
                    continue;

                const auto& port = portBase->as<PortSymbol>();

                // Only track input and inout ports
                if (port.direction == ArgumentDirection::In ||
                    port.direction == ArgumentDirection::InOut) {
                    inputPorts[port.name] = &port;
                }
            }

            // Get the port connections and mark connected ports
            for (auto conn : childInstance.getPortConnections()) {
                if (conn && conn->getExpression()) {
                    // Remove this port from the unconnected set
                    auto it = inputPorts.find(conn->port.name);
                    if (it != inputPorts.end()) {
                        inputPorts.erase(it);
                    }
                }
            }

            // Report any remaining unconnected input ports
            for (const auto& [name, port] : inputPorts) {
                diags.add(diag::UnconnectedInputPort, childInstance.location)
                    << childInstance.name << name;
            }
        }
    }
};

} // namespace unconnected_input_port

using namespace unconnected_input_port;

class UnconnectedInputPort : public TidyCheck {
public:
    [[maybe_unused]] explicit UnconnectedInputPort(
        TidyKind kind, std::optional<slang::DiagnosticSeverity> severity) :
        TidyCheck(kind, severity) {}

    bool check(const RootSymbol& root, const slang::analysis::AnalysisManager&) override {
        MainVisitor visitor(diagnostics);
        root.visit(visitor);
        return diagnostics.empty();
    }

    DiagCode diagCode() const override { return diag::UnconnectedInputPort; }

    std::string diagString() const override {
        return "instance {} has unconnected input port '{}'";
    }

    DiagnosticSeverity diagDefaultSeverity() const override { return DiagnosticSeverity::Warning; }

    std::string name() const override { return "UnconnectedInputPort"; }

    std::string description() const override { return shortDescription(); }

    std::string shortDescription() const override {
        return "Checks if module instantiations have unconnected input ports.";
    }
};

REGISTER(UnconnectedInputPort, UnconnectedInputPort, TidyKind::Synthesis)
