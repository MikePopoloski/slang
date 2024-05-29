#pragma once

#include "Debug.h"
#include "Netlist.h"
#include <memory>

#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/util/IntervalMap.h"

using namespace slang;

namespace netlist {

/// Visit proceural blocks. This visitor performs loop unrolling and handles
/// multiple map to the same variable.
class ProceduralBlockVisitor : public ast::ASTVisitor<ProceduralBlockVisitor, true, false> {
public:
    bool anyErrors = false;

    explicit ProceduralBlockVisitor(ast::Compilation& compilation, Netlist& netlist,
                                    ast::EdgeKind edgeKind) :
        netlist(netlist),
        evalCtx(ast::ASTContext(compilation.getRoot(), ast::LookupLocation::max)),
        edgeKind(edgeKind) {
        evalCtx.pushEmptyFrame();
        DEBUG_PRINT("Procedural block\n");
    }

    /// Determine the egde type to apply to map within a procedrual
    /// block.
    static ast::EdgeKind determineEdgeKind(ast::ProceduralBlockSymbol const& symbol) {
        ast::EdgeKind edgeKind = ast::EdgeKind::None;
        if (symbol.procedureKind == ast::ProceduralBlockKind::AlwaysFF ||
            symbol.procedureKind == ast::ProceduralBlockKind::Always) {
            auto tck = symbol.getBody().as<ast::TimedStatement>().timing.kind;
            if (tck == ast::TimingControlKind::SignalEvent) {
                edgeKind = symbol.getBody()
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
                    edgeKind = e->as<ast::SignalEventControl>().edge;
                    if (edgeKind == ast::EdgeKind::None)
                        break;
                }
                // if we got here, edgeKind is not "None" which is all we care about
            }
        }
        return edgeKind;
    }

    void handle(const ast::VariableSymbol& symbol) { netlist.addVariableDeclaration(symbol); }

    void handle(const ast::NetSymbol& symbol) { netlist.addVariableDeclaration(symbol); }

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

            // Pop the condition variables.
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

        // Add edges to the LHS target variables from declarations that
        // correspond to conditions controlling the assignment.
        for (auto* condNode : condVarsStack) {
            auto& condVarRef = condNode->as<NetlistVariableReference>();

            connectDeclToVar(condVarRef, condVarRef.symbol);
            for (auto* leftNode : visitorLHS.getVars()) {

                // Add edge from conditional variable to the LHS variable.
                connectVarToVar(*condNode, *leftNode);
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
    void connectVarToDecl(NetlistVariableReference& varNode,
                          ast::Symbol const& symbol) {
        auto* declNode = netlist.lookupVariable(resolveSymbolHierPath(symbol));
        netlist.addEdge(varNode, *declNode);
        DEBUG_PRINT("New edge: reference {} -> declaration {}\n", varNode.getName(), declNode->hierarchicalPath);
    }

    /// For the specified variable reference, create a dependency from the declaration or
    /// last definition.
    void connectDeclToVar(NetlistVariableReference& varNode, ast::Symbol const& symbol) {
        auto* declNode = netlist.lookupVariable(resolveSymbolHierPath(symbol));
        netlist.addEdge(*declNode, varNode);
        DEBUG_PRINT("New edge: declaration {} -> reference {}\n", declNode->hierarchicalPath,
                    varNode.getName());
    }

    void connectVarToVar(NetlistNode& sourceVarNode, NetlistNode& targetVarNode) {
        netlist.addEdge(sourceVarNode, targetVarNode);
        DEBUG_PRINT("New edge: reference {} -> reference {}\n", sourceVarNode.getName(),
                    targetVarNode.getName());
    }

    Netlist& netlist;
    ast::EvalContext evalCtx;
    SmallVector<NetlistNode*> condVarsStack;
    ast::EdgeKind edgeKind;
};

} // namespace netlist
