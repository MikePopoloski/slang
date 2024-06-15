//------------------------------------------------------------------------------
//! @file ContinuousAssignVisitor.h
//! @brief Visit continuous assignments as part of the construction of a netlist
//         graph.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "visitors/VariableReferenceVisitor.hpp"

using namespace slang;

namespace netlist {

/// An AST visitor to create dependencies between occurrances of variables
/// appearing on the left and right hand sides of continuous assignment statements.
class ContinuousAssignVisitor : public ast::ASTVisitor<ContinuousAssignVisitor, false, true> {
public:
    explicit ContinuousAssignVisitor(Netlist& netlist, ast::EvalContext& evalCtx,
                                     SmallVector<NetlistNode*>& condVars) :
        netlist(netlist), evalCtx(evalCtx), condVars(condVars) {}

    void connectDeclToVar(NetlistNode& declNode, const ast::Symbol& variable) {
        auto* varNode = netlist.lookupVariable(resolveSymbolHierPath(variable));
        netlist.addEdge(*varNode, declNode);
        DEBUG_PRINT("New edge: from declaration {} -> reference {}\n", varNode->hierarchicalPath,
                    declNode.getName());
    }

    void connectVarToDecl(NetlistNode& varNode, const ast::Symbol& declaration) {
        auto* declNode = netlist.lookupVariable(resolveSymbolHierPath(declaration));
        netlist.addEdge(varNode, *declNode);
        DEBUG_PRINT("New edge: reference {} -> declaration {}\n", varNode.getName(),
                    declNode->hierarchicalPath);
    }

    void connectVarToVar(NetlistNode& sourceVarNode, NetlistNode& targetVarNode) {
        netlist.addEdge(sourceVarNode, targetVarNode, ast::EdgeKind::None);
        DEBUG_PRINT("New edge: reference {} -> reference {}\n", sourceVarNode.getName(),
                    targetVarNode.getName());
    }

    void handle(const ast::AssignmentExpression& expr) {

        // Collect LHS variable references.
        VariableReferenceVisitor visitorLHS(netlist, evalCtx, true);
        expr.left().visit(visitorLHS);

        // Collect RHS variable references.
        VariableReferenceVisitor visitorRHS(netlist, evalCtx, false);
        expr.right().visit(visitorRHS);

        // For each variable reference occuring on the LHS of the assignment,
        // add an edge to variable declaration.
        for (auto* leftNode : visitorLHS.getVars()) {

            /// Create a dependency from the LSH variable back to the
            // declaration.
            connectVarToDecl(*leftNode, leftNode->symbol);

            // For each variable reference occuring on the RHS of the
            // assignment: add an edge from variable declaration and add an
            // edge to the LHS reference.
            for (auto* rightNode : visitorRHS.getVars()) {
                connectDeclToVar(*rightNode, rightNode->symbol);
                connectVarToVar(*rightNode, *leftNode);
            }
        }

        // Add edges to the LHS target variables from declarations that
        // correspond to conditions controlling the assignment.
        for (auto* condNode : condVars) {

            connectDeclToVar(*condNode, condNode->symbol);
            for (auto* leftNode : visitorLHS.getVars()) {

                // Add edge from conditional variable to the LHS variable.
                connectVarToVar(*condNode, *leftNode);
            }
        }
    }

private:
    Netlist& netlist;
    ast::EvalContext& evalCtx;
    SmallVector<NetlistNode*>& condVars;
};

} // namespace netlist
