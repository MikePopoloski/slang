//------------------------------------------------------------------------------
//! @file ProceduralBlockVisitor.h
//! @brief Visit procedural blocks as part of the construction of a netlist graph.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "Debug.h"
#include "Netlist.h"
#include "NetlistVisitorOptions.hpp"
#include "visitors/VariableReferenceVisitor.hpp"

#include "slang/ast/EvalContext.h"
#include "slang/ast/symbols/BlockSymbols.h"

using namespace slang;

namespace netlist {

/// Visit a proceural block. This visitor performs unrolling of loops and
/// evaluation of conditionals where the controlling conditions can be
/// determined statically.
class ProceduralBlockVisitor : public ast::ASTVisitor<ProceduralBlockVisitor, true, false> {
public:
    bool anyErrors = false;

    explicit ProceduralBlockVisitor(ast::Compilation& compilation, Netlist& netlist,
                                    NetlistVisitorOptions const& options, ast::EdgeKind edgeKind) :
        netlist(netlist), evalCtx(ast::ASTContext(compilation.getRoot(), ast::LookupLocation::max)),
        options(options), edgeKind(edgeKind) {
        evalCtx.pushEmptyFrame();
        DEBUG_PRINT("Procedural block\n");
    }

    /// Determine the egde type to apply to map within a procedrual
    /// block.
    static ast::EdgeKind determineEdgeKind(ast::ProceduralBlockSymbol const& symbol) {
        ast::EdgeKind result = ast::EdgeKind::None;
        if (symbol.procedureKind == ast::ProceduralBlockKind::AlwaysFF ||
            symbol.procedureKind == ast::ProceduralBlockKind::Always) {
            if (symbol.getBody().kind == ast::StatementKind::Block) {
                auto& block = symbol.getBody().as<ast::BlockStatement>();
                if (block.blockKind == ast::StatementBlockKind::Sequential &&
                    block.body.kind == ast::StatementKind::ConcurrentAssertion) {
                    return result;
                }
            }
            auto tck = symbol.getBody().as<ast::TimedStatement>().timing.kind;
            if (tck == ast::TimingControlKind::SignalEvent) {
                result = symbol.getBody()
                             .as<ast::TimedStatement>()
                             .timing.as<ast::SignalEventControl>()
                             .edge;
            }
            else if (tck == ast::TimingControlKind::EventList) {
                auto& events = symbol.getBody()
                                   .as<ast::TimedStatement>()
                                   .timing.as<ast::EventListControl>()
                                   .events;
                // We need to decide if this has the potential for combinatorial loops
                // The most strict test is if for any unique signal on the event list only one edge
                // (pos or neg) appears e.g. "@(posedge x or negedge x)" is potentially
                // combinatorial At the moment we'll settle for no signal having "None" edge.
                for (auto e : events) {
                    result = e->as<ast::SignalEventControl>().edge;
                    if (result == ast::EdgeKind::None)
                        break;
                }
                // If we got here, edgeKind is not "None" which is all we care about.
            }
        }
        return result;
    }

    void handle(const ast::VariableSymbol& symbol) { netlist.addVariableDeclaration(symbol); }

    void handle(const ast::NetSymbol& symbol) { netlist.addVariableDeclaration(symbol); }

    void handle(const ast::VariableDeclStatement& decl) {
        netlist.addVariableDeclaration(decl.symbol);
    }

    void handle(const ast::ForLoopStatement& loop) {

        // Conditions that mean this loop cannot be unrolled.
        if (!options.unrollForLoops || loop.loopVars.empty() || !loop.stopExpr ||
            loop.steps.empty() || anyErrors) {
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

            // Visit the 'then' and 'else' statements, whose execution is
            // under the control of the condition variables.
            stmt.ifTrue.visit(*this);
            if (stmt.ifFalse) {
                stmt.ifFalse->visit(*this);
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

        if (stmt.expr.kind == ast::ExpressionKind::Assignment) {
            handleAssignment(stmt.expr.as<ast::AssignmentExpression>());
        }
    }

    void handleAssignment(const ast::AssignmentExpression& expr) {

        // Collect LHS variable references.
        VariableReferenceVisitor visitorLHS(netlist, evalCtx, true);
        expr.left().visit(visitorLHS);

        // Collect RHS variable references.
        VariableReferenceVisitor visitorRHS(netlist, evalCtx, false);
        expr.right().visit(visitorRHS);

        // For each variable reference occuring on the LHS of the assignment,
        // add an edge to variable declaration.
        for (auto* leftNode : visitorLHS.getVars()) {
            auto& LHSVarRef = leftNode->as<NetlistVariableReference>();

            // Add edge from LHS variable refrence to variable declaration.
            connectVarToDecl(LHSVarRef, leftNode->symbol);

            // For each variable reference occuring on the RHS of the
            // assignment add an edge from variable declaration and add an
            // edge to the LHS reference. This needs to be extended to handle
            // concatenations properly.
            for (auto* rightNode : visitorRHS.getVars()) {
                auto& RHSVarRef = rightNode->as<NetlistVariableReference>();
                connectDeclToVar(RHSVarRef, RHSVarRef.symbol);
                connectVarToVar(RHSVarRef, LHSVarRef);
            }
        }
    }

private:
    bool step() {
        if (anyErrors || !evalCtx.step(SourceLocation::NoLocation)) {
            anyErrors = true;
            return false;
        }
        return true;
    }

    /// For the specified variable reference, create a dependency to the declaration or
    /// last definition.
    void connectVarToDecl(NetlistVariableReference& varNode, ast::Symbol const& symbol) {
        auto* declNode = netlist.lookupVariable(resolveSymbolHierPath(symbol));
        netlist.addEdge(varNode, *declNode);
        DEBUG_PRINT("New edge: reference {} -> declaration {}\n", varNode.getName(),
                    declNode->hierarchicalPath);
    }

    /// For the specified variable reference, create a dependency from the declaration or
    /// last definition.
    void connectDeclToVar(NetlistVariableReference& varNode, ast::Symbol const& symbol) {
        auto* declNode = netlist.lookupVariable(resolveSymbolHierPath(symbol));
        netlist.addEdge(*declNode, varNode);
        DEBUG_PRINT("New edge: declaration {} -> reference {}\n", declNode->hierarchicalPath,
                    varNode.getName());
    }

    /// For the specified varaible references, create a dependency between
    /// them. This represents an assignment.
    void connectVarToVar(NetlistNode& sourceVarNode, NetlistNode& targetVarNode) {
        netlist.addEdge(sourceVarNode, targetVarNode, edgeKind);
        DEBUG_PRINT("New edge: reference {} -> reference {} by edge {}\n", sourceVarNode.getName(),
                    targetVarNode.getName(), toString(edgeKind));
    }

    Netlist& netlist;
    ast::EvalContext evalCtx;
    NetlistVisitorOptions const& options;
    ast::EdgeKind edgeKind;
};

} // namespace netlist
