//------------------------------------------------------------------------------
//! @file SplitVariables.h
//! @brief Transform netlist variable nodes to reflect connections with
///        structured variables.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "Netlist.h"
#include "fmt/color.h"
#include "fmt/format.h"
#include <utility>

#include "slang/ast/types/Type.h"
#include "slang/util/Util.h"

namespace netlist {

/// A class to perform a transformation on the netlist to split variable
/// declaration nodes of structured types into multiple parts based on the
/// types of the incoming and outgoing edges.
class SplitVariables {
public:
    SplitVariables(Netlist& netlist) : netlist(netlist) { split(); }

private:
    /// Given two ranges [end1:start1] and [end2:start2], return true if there is
    /// any overlap in values between them.
    inline bool rangesOverlap(size_t start1, size_t end1, size_t start2, size_t end2) const {
        return start1 <= end2 && start2 <= end1;
    }

    /// Return true if the selection made by the target node intersects with the
    /// selection made by the source node.
    bool isIntersectingSelection(NetlistVariableReference& sourceNode,
                                 NetlistVariableReference& targetNode) const {
        bool match = true;
        size_t selectorDepth = 0;
        while (match) {
            // Terminate the loop if either variable reference has no further
            // selectors.
            if (selectorDepth >= sourceNode.selectors.size() ||
                selectorDepth >= targetNode.selectors.size()) {
                break;
            }
            auto& sourceSelector = sourceNode.selectors[selectorDepth];
            auto& targetSelector = targetNode.selectors[selectorDepth];
            SLANG_ASSERT(sourceSelector->kind == targetSelector->kind && "selectors do not match");
            switch (sourceSelector->kind) {
                case VariableSelectorKind::ElementSelect:
                    // Matching selectors if the index is the same.
                    match = sourceSelector->as<VariableElementSelect>().getIndexInt() ==
                            targetSelector->as<VariableElementSelect>().getIndexInt();
                    break;
                case VariableSelectorKind::RangeSelect: {
                    // Matching selectors if there is any overlap in the two ranges.
                    auto sourceRangeSel = sourceSelector->as<VariableRangeSelect>();
                    auto targetRangeSel = targetSelector->as<VariableRangeSelect>();
                    auto srcLeft = sourceRangeSel.getLeftIndexInt();
                    auto srcRight = sourceRangeSel.getRightIndexInt();
                    auto tgtLeft = targetRangeSel.getLeftIndexInt();
                    auto tgtRight = targetRangeSel.getRightIndexInt();
                    match = rangesOverlap(srcRight, srcLeft, tgtRight, tgtLeft);
                    break;
                }
                case VariableSelectorKind::MemberAccess:
                    // Matching selectors if the member names match.
                    match = sourceSelector->as<VariableMemberAccess>().name ==
                            targetSelector->as<VariableMemberAccess>().name;
                    break;
            }
            selectorDepth++;
        }
        return match;
    }

    void split() {
        std::vector<std::tuple<NetlistVariableDeclaration*, NetlistEdge*, NetlistEdge*>>
            modifications;
        // Find each variable declaration nodes in the graph that has multiple
        // outgoing edges.
        for (auto& node : netlist) {
            if (node->kind == NodeKind::VariableDeclaration && node->outDegree() > 1) {
                auto& varDeclNode = node->as<NetlistVariableDeclaration>();
                auto& varType = varDeclNode.symbol.getDeclaredType()->getType();
                DEBUG_PRINT(fmt::format("Variable {} has type {}\n", varDeclNode.hierarchicalPath,
                                        varType.toString()));
                std::vector<NetlistEdge*> inEdges;
                netlist.getInEdgesToNode(*node, inEdges);
                // Find pairs of input and output edges that are attached to variable
                // refertence nodes. Eg.
                //   var ref -> var decl -> var ref
                // If the variable references select the same part of a structured
                // variable, then transform them into:
                //   var ref -> var alias -> var ref
                // And mark the original edges as disabled.
                for (auto* inEdge : inEdges) {
                    for (auto& outEdge : *node) {
                        if (inEdge->getSourceNode().kind == NodeKind::VariableReference &&
                            outEdge->getTargetNode().kind == NodeKind::VariableReference) {
                            auto& sourceVarRef =
                                inEdge->getSourceNode().as<NetlistVariableReference>();
                            auto& targetVarRef =
                                outEdge->getTargetNode().as<NetlistVariableReference>();
                            auto match = isIntersectingSelection(sourceVarRef, targetVarRef);
                            if (match) {
                                DEBUG_PRINT(
                                    fmt::format("New dependency through variable {} -> {}\n",
                                                sourceVarRef.toString(), targetVarRef.toString()));
                                modifications.emplace_back(&varDeclNode, inEdge, outEdge.get());
                            }
                        }
                    }
                }
            }
        }
        // Apply the operations to the graph.
        for (auto& modification : modifications) {
            auto* varDeclNode = std::get<0>(modification);
            auto* inEdge = std::get<1>(modification);
            auto* outEdge = std::get<2>(modification);
            // Disable the existing edges.
            inEdge->disable();
            outEdge->disable();
            // Create a new node that aliases the variable declaration.
            auto& varAliasNode = netlist.addVariableAlias(varDeclNode->symbol);
            // Create edges through the new node.
            inEdge->getSourceNode().addEdge(varAliasNode);
            varAliasNode.addEdge(outEdge->getTargetNode());
        }
    }

private:
    Netlist& netlist;
};

} // namespace netlist
