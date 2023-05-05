#pragma once

#include "fmt/color.h"
#include "fmt/format.h"

#include "slang/ast/types/Type.h"

#include "Netlist.h"

namespace netlist {

/// A class to perform a transformation on the netlist to split variable
/// declaration nodes of structured types into multiple parts based on the
/// types of the incoming and outgoing edges.
class SplitVariables {
public:
  SplitVariables(Netlist &netlist) : netlist(netlist) {
    split();
  }

private:
  /// Return true if the selection made by the target node matches the
  /// selection made by the source node.
  bool isMatchingSelection(const ast::Type &varType,
                           NetlistNode &sourceNode,
                           NetlistNode &targetNode) {
    return false;
  }

  void split() {
    for (auto &node : netlist) {
      if (node->kind == NodeKind::VariableDeclaration) {
        auto &varDeclNode = node->as<NetlistVariableDeclaration>();
        auto &varType = varDeclNode.symbol.getDeclaredType()->getType();
        DEBUG_PRINT(fmt::format("Var {} has type {}\n", varDeclNode.hierarchicalPath,
                                                        varType.toString()));
        std::vector<NetlistEdge*> inEdges;
        netlist.getInEdgesToNode(*node, inEdges);
        for (auto *inEdge : inEdges) {
          for (auto &outEdge : *node) {
            auto match = isMatchingSelection(varType, inEdge->getSourceNode(), outEdge->getTargetNode());
            if (match) {
              DEBUG_PRINT(fmt::format("{} -> {}\n",
                                      inEdge->getSourceNode().toString(),
                                      outEdge->getTargetNode().toString()));
            }
          }
        }
      }
    }
  }

private:
  Netlist &netlist;
};

} // End namespace netlist.
