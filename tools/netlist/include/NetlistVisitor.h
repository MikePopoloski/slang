//------------------------------------------------------------------------------
//! @file NetlistVisitor.h
//! @brief An AST visitor (and sub visitors) to construct a netlist
//         representation.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "Config.h"
#include "Debug.h"
#include "Netlist.h"
#include "fmt/color.h"
#include "fmt/format.h"
#include <iostream>

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/ast/Symbol.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/util/Util.h"

using namespace slang;

namespace netlist {

static std::string getSymbolHierPath(const ast::Symbol& symbol) {
    std::string buffer;
    symbol.getHierarchicalPath(buffer);
    return buffer;
}

static void connectDeclToVar(Netlist& netlist, NetlistNode& varNode,
                             const std::string& hierarchicalPath) {
    auto* variableNode = netlist.lookupVariable(hierarchicalPath);
    netlist.addEdge(*variableNode, varNode);
    DEBUG_PRINT(
        fmt::format("Edge decl {} to ref {}\n", variableNode->getName(), varNode.getName()));
}

static void connectVarToDecl(Netlist& netlist, NetlistNode& varNode,
                             const std::string& hierarchicalPath) {
    auto* portNode = netlist.lookupVariable(hierarchicalPath);
    netlist.addEdge(varNode, *portNode);
    DEBUG_PRINT(
        fmt::format("Edge ref {} to port ref {}\n", varNode.getName(), portNode->getName()));
}

static void connectVarToVar(Netlist& netlist, NetlistNode& sourceVarNode,
                            NetlistNode& targetVarNode) {
    netlist.addEdge(sourceVarNode, targetVarNode);
    DEBUG_PRINT(
        fmt::format("Edge ref {} to ref {}\n", sourceVarNode.getName(), targetVarNode.getName()));
}

/// An AST visitor to identify variable references with selectors in
/// expressions, adding them to a visit list during the traversal.
class VariableReferenceVisitor : public ast::ASTVisitor<VariableReferenceVisitor, false, true> {
public:
    explicit VariableReferenceVisitor(Netlist& netlist, ast::EvalContext& evalCtx,
                                      bool leftOperand = false) :
        netlist(netlist),
        evalCtx(evalCtx), leftOperand(leftOperand) {}

    void handle(const ast::NamedValueExpression& expr) {
        auto& node = netlist.addVariableReference(expr.symbol, expr, leftOperand);
        varList.push_back(&node);
        for (auto* selector : selectors) {
            if (selector->kind == ast::ExpressionKind::ElementSelect) {
                auto index = selector->as<ast::ElementSelectExpression>().selector().eval(evalCtx);
                node.addElementSelect(index);
            }
            else if (selector->kind == ast::ExpressionKind::RangeSelect) {
                auto& rangeSelectExpr = selector->as<ast::RangeSelectExpression>();
                auto leftIndex = rangeSelectExpr.left().eval(evalCtx);
                auto rightIndex = rangeSelectExpr.right().eval(evalCtx);
                node.addRangeSelect(leftIndex, rightIndex);
            }
            else if (selector->kind == ast::ExpressionKind::MemberAccess) {
                node.addMemberAccess(selector->as<ast::MemberAccessExpression>().member.name);
            }
        }
        selectors.clear();
    }

    void handle(const ast::ElementSelectExpression& expr) {
        selectors.push_back(&expr);
        expr.value().visit(*this);
    }

    void handle(const ast::RangeSelectExpression& expr) {
        selectors.push_back(&expr);
        expr.value().visit(*this);
    }

    void handle(const ast::MemberAccessExpression& expr) {
        selectors.push_back(&expr);
        expr.value().visit(*this);
    }

    std::vector<NetlistNode*>& getVars() { return varList; }

private:
    Netlist& netlist;
    ast::EvalContext& evalCtx;
    /// Whether this traversal is the target of an assignment or not.
    bool leftOperand;
    std::vector<NetlistNode*> varList;
    std::vector<const ast::Expression*> selectors;
};

/// An AST visitor to create dependencies between occurrances of variables
/// appearing on the left and right hand sides of assignment statements.
class AssignmentVisitor : public ast::ASTVisitor<AssignmentVisitor, false, true> {
public:
    explicit AssignmentVisitor(Netlist& netlist, ast::EvalContext& evalCtx,
                               SmallVector<NetlistNode*>& condVars) :
        netlist(netlist),
        evalCtx(evalCtx), condVars(condVars) {}

    void handle(const ast::AssignmentExpression& expr) {
        // Collect variable references on the left-hand side of the assignment.
        VariableReferenceVisitor visitorLHS(netlist, evalCtx, true);
        expr.left().visit(visitorLHS);
        // Collect variable references on the right-hand side of the assignment.
        VariableReferenceVisitor visitorRHS(netlist, evalCtx, false);
        expr.right().visit(visitorRHS);
        for (auto* leftNode : visitorLHS.getVars()) {
            // Add edge from LHS variable refrence to variable declaration.
            connectVarToDecl(netlist, *leftNode, getSymbolHierPath(leftNode->symbol));
            for (auto* rightNode : visitorRHS.getVars()) {
                // Add edge from variable declaration to RHS variable reference.
                connectDeclToVar(netlist, *rightNode, getSymbolHierPath(rightNode->symbol));
                // Add edge form RHS expression term to LHS expression terms.
                connectVarToVar(netlist, *rightNode, *leftNode);
            }
        }
        for (auto* condNode : condVars) {
            // Add edge from conditional variable declaraiton to the reference.
            connectDeclToVar(netlist, *condNode, getSymbolHierPath(condNode->symbol));
            for (auto* leftNode : visitorLHS.getVars()) {
                // Add edge from conditional variable to the LHS variable.
                connectVarToVar(netlist, *condNode, *leftNode);
            }
        }
    }

private:
    Netlist& netlist;
    ast::EvalContext& evalCtx;
    SmallVector<NetlistNode*>& condVars;
};

/// An AST visitor for proceural blocks that performs loop unrolling.
class ProceduralBlockVisitor : public ast::ASTVisitor<ProceduralBlockVisitor, true, false> {
public:
    bool anyErrors = false;

    explicit ProceduralBlockVisitor(ast::Compilation& compilation, Netlist& netlist) :
        netlist(netlist), evalCtx(compilation) {
        evalCtx.pushEmptyFrame();
    }

    void handle(const ast::ForLoopStatement& loop) {

        // Conditions this loop cannot be unrolled.
        if (loop.loopVars.empty() || !loop.stopExpr || loop.steps.empty() || anyErrors) {
            loop.body.visit(*this);
            return;
        }

        // Attempt to unroll the loop. If we are unable to collect constant values
        // for all loop variables across all iterations, we won't unroll at all.
        auto handleFail = [&] {
            for (auto var : loop.loopVars) {
                evalCtx.deleteLocal(var);
            }
            loop.body.visit(*this);
        };

        // Create a list of the initialised loop variables.
        SmallVector<ConstantValue*> localPtrs;
        for (auto var : loop.loopVars) {
            auto init = var->getInitializer();
            if (!init) {
                handleFail();
                return;
            }

            auto cv = init->eval(evalCtx);
            if (!cv) {
                handleFail();
                return;
            }

            localPtrs.push_back(evalCtx.createLocal(var, std::move(cv)));
        }

        // Create a list of all the loop variable values across all iterations.
        SmallVector<ConstantValue, 16> values;
        while (true) {
            auto cv = step() ? loop.stopExpr->eval(evalCtx) : ConstantValue();
            if (!cv) {
                handleFail();
                return;
            }

            if (!cv.isTrue()) {
                break;
            }

            for (auto local : localPtrs) {
                values.emplace_back(*local);
            }

            for (auto step : loop.steps) {
                if (!step->eval(evalCtx)) {
                    handleFail();
                    return;
                }
            }
        }

        // We have all the loop iteration values. Go back through
        // and visit the loop body for each iteration.
        for (size_t i = 0; i < values.size();) {
            for (auto local : localPtrs) {
                *local = std::move(values[i++]);
            }

            loop.body.visit(*this);
            if (anyErrors) {
                return;
            }
        }
    }

    void handle(const ast::ConditionalStatement& stmt) {
        // Evaluate the condition; if not constant visit both sides (the
        // fallback option), otherwise visit only the side that matches the
        // condition.

        auto fallback = [&] {
            // Create a list of variables appearing in the condition
            // expression.
            VariableReferenceVisitor varRefVisitor(netlist, evalCtx);
            for (auto& cond : stmt.conditions) {
                if (cond.pattern) {
                    // Skip.
                    continue;
                }
                cond.expr->visit(varRefVisitor);
            }

            // Push the condition variables.
            for (auto& varRef : varRefVisitor.getVars()) {
                condVarsStack.push_back(varRef);
            }

            // Visit the 'then' and 'else' statements, whose execution is
            // under the control of the condition variables.
            stmt.ifTrue.visit(*this);
            if (stmt.ifFalse) {
                stmt.ifFalse->visit(*this);
            }

            // Pop the conditon variables.
            for (auto& varRef : varRefVisitor.getVars()) {
                condVarsStack.pop_back();
            }
        };

        for (auto& cond : stmt.conditions) {
            if (cond.pattern || !step()) {
                fallback();
                return;
            }

            auto result = cond.expr->eval(evalCtx);
            if (!result) {
                fallback();
                return;
            }

            if (!result.isTrue()) {
                if (stmt.ifFalse) {
                    stmt.ifFalse->visit(*this);
                }
                return;
            }
        }

        stmt.ifTrue.visit(*this);
    }

    void handle(const ast::ExpressionStatement& stmt) {
        step();
        AssignmentVisitor visitor(netlist, evalCtx, condVarsStack);
        stmt.visit(visitor);
    }

private:
    bool step() {
        if (anyErrors || !evalCtx.step(SourceLocation::NoLocation)) {
            anyErrors = true;
            return false;
        }
        return true;
    }

    Netlist& netlist;
    ast::EvalContext evalCtx;
    SmallVector<NetlistNode*> condVarsStack;
};

/// A visitor that traverses the AST and builds a netlist representation.
class NetlistVisitor : public ast::ASTVisitor<NetlistVisitor, true, false> {
public:
    explicit NetlistVisitor(ast::Compilation& compilation, Netlist& netlist) :
        compilation(compilation), netlist(netlist) {}

    /// Connect ports of a module instance to their corresponding variables.
    void connectInstancePort(NetlistNode& port) {
        if (auto* internalSymbol = port.symbol.as<ast::PortSymbol>().internalSymbol) {
            std::string pathBuffer;
            internalSymbol->getHierarchicalPath(pathBuffer);
            auto* variableNode = netlist.lookupVariable(pathBuffer);
            switch (port.symbol.as<ast::PortSymbol>().direction) {
                case ast::ArgumentDirection::In:
                    netlist.addEdge(port, *variableNode);
                    break;
                case ast::ArgumentDirection::Out:
                    netlist.addEdge(*variableNode, port);
                    break;
                case ast::ArgumentDirection::InOut:
                    netlist.addEdge(port, *variableNode);
                    netlist.addEdge(*variableNode, port);
                    break;
                case ast::ArgumentDirection::Ref:
                    break;
            }
        }
        else {
            SLANG_UNREACHABLE;
        }
    }

    /// Variable declaration.
    void handle(const ast::VariableSymbol& symbol) {}

    /// Net declaration.
    void handle(const ast::NetSymbol& symbol) {}

    /// Port declaration.
    void handle(const ast::PortSymbol& symbol) {}

    /// Instance.
    void handle(const ast::InstanceSymbol& symbol) {
        DEBUG_PRINT(fmt::format("Instance {}\n", symbol.name));
        if (symbol.name.empty()) {
            // An instance without a name has been excluded from the design.
            // This can happen when the --top option is used and there is an
            // uninstanced module.
            return;
        }
        // Body members.
        // Variables first.
        for (auto& member : symbol.body.members()) {
            if (member.kind == ast::SymbolKind::Variable || member.kind == ast::SymbolKind::Net) {
                netlist.addVariableDeclaration(member);
            }
        }
        // Then ports.
        for (auto& member : symbol.body.members()) {
            if (member.kind == ast::SymbolKind::Port) {
                // Create the port declaration netlist node.
                auto& portNode = netlist.addPortDeclaration(member);
                // Connected to to the corresponding local variable.
                connectInstancePort(portNode);
            }
        }
        // Handle connections to the ports of the instance.
        for (auto* portConnection : symbol.getPortConnections()) {
            // Collect variable references in the port expression.
            ast::EvalContext evalCtx(compilation);
            auto portDirection = portConnection->port.as<ast::PortSymbol>().direction;
            // The port is effectively the target of an assignment if it is an
            // input.
            bool isLeftOperand = portDirection == ast::ArgumentDirection::In ||
                                 portDirection == ast::ArgumentDirection::InOut;
            VariableReferenceVisitor visitor(netlist, evalCtx, isLeftOperand);
            portConnection->getExpression()->visit(visitor);
            // Given a port hookup of the form:
            //   .foo(expr(x, y))
            // Where expr() is an expression involving some variables.
            // Then, add the following edges:
            // Input port:
            //   var decl x -> var ref x -> port var ref foo
            // Output port:
            //   var decl y <- var ref y <- port var ref foo
            // InOut port:
            //   var decl x -> var ref x -> port var ref foo
            //   var decl y <- var ref y <- port var ref foo
            for (auto* node : visitor.getVars()) {
                switch (portDirection) {
                    case ast::ArgumentDirection::In:
                        connectDeclToVar(netlist, *node, getSymbolHierPath(node->symbol));
                        connectVarToDecl(netlist, *node, getSymbolHierPath(portConnection->port));
                        break;
                    case ast::ArgumentDirection::Out:
                        connectDeclToVar(netlist, *node, getSymbolHierPath(portConnection->port));
                        connectVarToDecl(netlist, *node, getSymbolHierPath(node->symbol));
                        break;
                    case ast::ArgumentDirection::InOut:
                        connectDeclToVar(netlist, *node, getSymbolHierPath(node->symbol));
                        connectDeclToVar(netlist, *node, getSymbolHierPath(portConnection->port));
                        connectVarToDecl(netlist, *node, getSymbolHierPath(node->symbol));
                        connectVarToDecl(netlist, *node, getSymbolHierPath(portConnection->port));
                        break;
                    case ast::ArgumentDirection::Ref:
                        break;
                }
            }
        }
        symbol.body.visit(*this);
    }

    /// Procedural block.
    void handle(const ast::ProceduralBlockSymbol& symbol) {
        ProceduralBlockVisitor visitor(compilation, netlist);
        symbol.visit(visitor);
    }

    /// Continuous assignment statement.
    void handle(const ast::ContinuousAssignSymbol& symbol) {
        ast::EvalContext evalCtx(compilation);
        SmallVector<NetlistNode*> condVars;
        AssignmentVisitor visitor(netlist, evalCtx, condVars);
        symbol.visit(visitor);
    }

private:
    ast::Compilation& compilation;
    Netlist& netlist;
};

} // namespace netlist
