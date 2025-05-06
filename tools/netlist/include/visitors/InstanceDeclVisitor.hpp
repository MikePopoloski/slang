//------------------------------------------------------------------------------
//! @file InstanceDeclVisitor.h
//! @brief Visit instances as part of the construction of a netlist graph.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "VariableReferenceVisitor.hpp"

#include "slang/ast/EvalContext.h"

using namespace slang;

namespace netlist {

/// Visit module and interface instances to perform hookup of external
/// variables to the corresponding ports and then to internally-scoped
/// variables mirroring the ports.
class InstanceDeclVisitor : public ast::ASTVisitor<InstanceDeclVisitor, true, false> {
public:
    explicit InstanceDeclVisitor(ast::Compilation& compilation, Netlist& netlist) :
        compilation(compilation), netlist(netlist) {}

private:
    /// Connect the ports of a module instance to their corresponding variables
    /// occuring in the body of the module.
    void connectPortInternal(NetlistNode& port) {
        if (auto* internalSymbol = port.symbol.as<ast::PortSymbol>().internalSymbol) {
            auto pathBuffer = internalSymbol->getHierarchicalPath();

            auto* variableNode = netlist.lookupVariable(pathBuffer);
            switch (port.symbol.as<ast::PortSymbol>().direction) {
                case ast::ArgumentDirection::In:
                    netlist.addEdge(port, *variableNode);
                    DEBUG_PRINT("New edge: input port {} -> variable {}\n", port.symbol.name,
                                pathBuffer);
                    break;
                case ast::ArgumentDirection::Out:
                    netlist.addEdge(*variableNode, port);
                    DEBUG_PRINT("New edge: variable {} -> output port {}\n", pathBuffer,
                                port.symbol.name);
                    break;
                case ast::ArgumentDirection::InOut:
                    netlist.addEdge(port, *variableNode);
                    netlist.addEdge(*variableNode, port);
                    DEBUG_PRINT("New edges: variable {} <-> inout port {}\n", pathBuffer,
                                port.symbol.name);
                    break;
                case ast::ArgumentDirection::Ref:
                    break;
            }
        }
        else {
            SLANG_UNREACHABLE;
        }
    }

    /// Create instance variable declarations.
    auto handleInstanceMemberVars(ast::InstanceSymbol const& symbol) {

        for (auto& member : symbol.body.members()) {
            if (member.kind == ast::SymbolKind::Variable || member.kind == ast::SymbolKind::Net) {
                netlist.addVariableDeclaration(member);
            }
        }
    }

    /// Create instance port declarations. Must be called after
    /// handleInstanceMemberVars() in order that ports can be connected to
    /// their corresponding variables.
    auto handleInstanceMemberPorts(ast::InstanceSymbol const& symbol) {

        for (auto& member : symbol.body.members()) {
            if (member.kind == ast::SymbolKind::Port) {
                // Create the port declaration netlist node and connect it to
                // the corresponding local variable declaration.
                auto& portNode = netlist.addPortDeclaration(member);
                connectPortInternal(portNode);
            }
        }
    }

public:
    /// Variable declaration (deferred to handleInstanceMemberVars).
    void handle(const ast::VariableSymbol& symbol) {}

    /// Net declaration (deferred to handleInstanceMemberVars).
    void handle(const ast::NetSymbol& symbol) {}

    /// Port declaration (deferred to handleInstanceMemberPorts).
    void handle(const ast::PortSymbol& symbol) {}

    /// Instance.
    void handle(const ast::InstanceSymbol& symbol) {
        DEBUG_PRINT("Instance: {}\n", symbol.getHierarchicalPath());

        if (symbol.getHierarchicalPath() == "$unit") {
            // An instance without a name has been excluded from the design.
            // This can happen when the --top option is used and there is an
            // uninstanced module.
            return;
        }

        handleInstanceMemberVars(symbol);
        handleInstanceMemberPorts(symbol);

        symbol.body.visit(*this);
    }

private:
    ast::Compilation& compilation;
    Netlist& netlist;
};

} // namespace netlist
