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

/// Visit module and interface instances to dispatch visitors for procedural
/// blocks, generate blocks and continuous assignments.
class InstanceVisitor : public ast::ASTVisitor<InstanceVisitor, true, false> {
public:
    explicit InstanceVisitor(ast::Compilation& compilation, Netlist& netlist,
                             NetlistVisitorOptions const& options) :
        compilation(compilation), netlist(netlist), options(options) {}

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

    /// Instance.
    void handle(const ast::InstanceSymbol& symbol) {
        DEBUG_PRINT("Instance: {}\n", symbol.getHierarchicalPath());

        if (symbol.getHierarchicalPath() == "$unit") {
            // An instance without a name has been excluded from the design.
            // This can happen when the --top option is used and there is an
            // uninstanced module.
            return;
        }

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
