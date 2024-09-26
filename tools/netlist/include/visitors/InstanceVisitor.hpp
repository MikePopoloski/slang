//------------------------------------------------------------------------------
//! @file InstanceVisitor.h
//! @brief Visit instances as part of the construction of a netlist graph.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "visitors/ContinuousAssignVisitor.hpp"
#include "visitors/GenerateBlockVisitor.hpp"

using namespace slang;

namespace netlist {

/// Visit module and interface instances to perform hookup of external
/// variables to the corresponding ports and then to internally-scoped
/// variables mirroring the ports.
class InstanceVisitor : public ast::ASTVisitor<InstanceVisitor, true, false> {
public:
    explicit InstanceVisitor(ast::Compilation& compilation, Netlist& netlist,
                             NetlistVisitorOptions const& options) :
        compilation(compilation), netlist(netlist), options(options) {}

private:
    void connectDeclToVar(NetlistNode& declNode, const ast::Symbol& variable) {
        auto* varNode = netlist.lookupVariable(resolveSymbolHierPath(variable));
        netlist.addEdge(*varNode, declNode);
        DEBUG_PRINT("New edge: from declaration {} to reference {}\n", varNode->hierarchicalPath,
                    declNode.getName());
    }

    void connectVarToDecl(NetlistNode& varNode, const ast::Symbol& declaration) {
        auto* declNode = netlist.lookupVariable(resolveSymbolHierPath(declaration));
        netlist.addEdge(varNode, *declNode);
        DEBUG_PRINT("New edge: reference {} to declaration {}\n", varNode.getName(),
                    declNode->hierarchicalPath);
    }

    /// Connect the ports of a module instance to the variables that connect to
    /// it in the parent scope. Given a port hookup of the form:
    ///
    ///   .foo(expr(x, y))
    ///
    /// Where expr() is an expression involving some variables.
    ///
    /// Then, add the following edges:
    ///
    /// - Input port:
    ///
    ///   var decl x -> var ref x -> port var ref foo
    ///
    /// - Output port:
    ///
    ///   var decl y <- var ref y <- port var ref foo
    ///
    /// - InOut port:
    ///
    ///   var decl x -> var ref x -> port var ref foo
    ///   var decl y <- var ref y <- port var ref foo
    void connectPortExternal(NetlistNode* node, ast::Symbol const& portSymbol,
                             ast::ArgumentDirection direction) {
        switch (direction) {
            case ast::ArgumentDirection::In:
                connectDeclToVar(*node, node->symbol);
                connectVarToDecl(*node, portSymbol);
                break;
            case ast::ArgumentDirection::Out:
                connectDeclToVar(*node, portSymbol);
                connectVarToDecl(*node, node->symbol);
                break;
            case ast::ArgumentDirection::InOut:
                connectDeclToVar(*node, node->symbol);
                connectDeclToVar(*node, portSymbol);
                connectVarToDecl(*node, node->symbol);
                connectVarToDecl(*node, portSymbol);
                break;
            case ast::ArgumentDirection::Ref:
                break;
        }
    }

    /// Connect the ports of a module instance to their corresponding variables
    /// occuring in the body of the module.
    void connectPortInternal(NetlistNode& port) {
        if (auto* internalSymbol = port.symbol.as<ast::PortSymbol>().internalSymbol) {
            std::string pathBuffer;
            internalSymbol->getHierarchicalPath(pathBuffer);
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

    // Handle making connections from the port connections to the port
    // declarations of an instance.
    auto handleInstanceExtPorts(ast::InstanceSymbol const& symbol) {

        for (auto* portConnection : symbol.getPortConnections()) {

            if (portConnection->port.kind == ast::SymbolKind::Port) {
                auto& port = portConnection->port.as<ast::PortSymbol>();
                auto direction = portConnection->port.as<ast::PortSymbol>().direction;

                ast::EvalContext evalCtx(
                    ast::ASTContext(compilation.getRoot(), ast::LookupLocation::max));

                // The port is the target of an assignment if it is an input.
                bool isLeftOperand = direction == ast::ArgumentDirection::In ||
                                     direction == ast::ArgumentDirection::InOut;

                if (portConnection->getExpression() == nullptr) {
                    // Empty port hookup so skip.
                    continue;
                }

                // Collect variable references in the port expression.
                VariableReferenceVisitor visitor(netlist, evalCtx, isLeftOperand);
                portConnection->getExpression()->visit(visitor);

                for (auto* node : visitor.getVars()) {
                    connectPortExternal(node, portConnection->port, direction);
                }
            }
            else if (portConnection->port.kind == ast::SymbolKind::InterfacePort) {
                // Skip
            }
            else {
                SLANG_UNREACHABLE;
            }
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
        DEBUG_PRINT("Instance: {}\n", getSymbolHierPath(symbol));

        if (getSymbolHierPath(symbol) == "$unit") {
            // An instance without a name has been excluded from the design.
            // This can happen when the --top option is used and there is an
            // uninstanced module.
            return;
        }

        handleInstanceMemberVars(symbol);
        handleInstanceMemberPorts(symbol);
        handleInstanceExtPorts(symbol);

        symbol.body.visit(*this);
    }

    /// Procedural block.
    void handle(const ast::ProceduralBlockSymbol& symbol) {
        ProceduralBlockVisitor visitor(compilation, netlist, options,
                                       ProceduralBlockVisitor::determineEdgeKind(symbol));
        symbol.visit(visitor);
    }

    /// Generate block.
    void handle(const ast::GenerateBlockSymbol& symbol) {
        if (!symbol.isUninstantiated) {
            GenerateBlockVisitor visitor(compilation, netlist, options);
            symbol.visit(visitor);
        }
    }

    /// Continuous assignment statement.
    void handle(const ast::ContinuousAssignSymbol& symbol) {
        ast::EvalContext evalCtx(ast::ASTContext(compilation.getRoot(), ast::LookupLocation::max));
        SmallVector<NetlistNode*> condVars;
        ContinuousAssignVisitor visitor(netlist, evalCtx, condVars);
        symbol.visit(visitor);
    }

private:
    ast::Compilation& compilation;
    Netlist& netlist;
    NetlistVisitorOptions const& options;
};

} // namespace netlist
