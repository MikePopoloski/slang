#pragma once

#include <map>
#include <vector>

#include "Netlist.h"
#include "NetlistPath.h"
#include "DepthFirstSearch.h"

namespace netlist {

class PathFinder {
private:
  /// Depth-first traversal produces a tree sub graph and as such, each node
  /// can only have one parent node. This map captures these relationships and
  /// is used to determine paths between leaf nodes and the root node of the
  /// tree.
  using TraversalMap = std::map<Netlist::node_descriptor, Netlist::node_descriptor>;

  class Visitor : public DepthFirstSearchVisitor<NetlistNode, NetlistEdge> {
  public:
    Visitor(Netlist &netlist, TraversalMap &traversalMap)
      : netlist(netlist), traversalMap(traversalMap) {}
    void visitNode(NetlistNode &node) override {
    }
    void visitEdge(NetlistEdge &edge) override {
      auto sourceDesc = netlist.getNodeDescriptor(edge.getSourceNode());
      auto targetDesc = netlist.getNodeDescriptor(edge.getTargetNode());
      assert(traversalMap.count(targetDesc) == 0 && "node cannot have two parents");
      traversalMap[targetDesc] = sourceDesc;
    }
  private:
    Netlist &netlist;
    TraversalMap &traversalMap;
  };

public:

  PathFinder(Netlist &netlist) : netlist(netlist) {}

  NetlistPath buildPath(TraversalMap &traversalMap,
                        NetlistNode &startNode,
                        NetlistNode &endNode) {
    // Single-node path.
    if (startNode == endNode) {
      return NetlistPath({&endNode});
    }
    // Empty path.
    if (traversalMap.count(netlist.getNodeDescriptor(endNode)) == 0) {
      return NetlistPath();
    }
    // Multi-node path.
    NetlistPath path({&endNode});
    auto startNodeDesc = netlist.getNodeDescriptor(startNode);
    auto nextNodeDesc = netlist.getNodeDescriptor(endNode);
    do {
      nextNodeDesc = traversalMap[nextNodeDesc];
      path.add(netlist.getNode(nextNodeDesc));
    } while (nextNodeDesc != startNodeDesc);
    return path;
  }

  NetlistPath find(NetlistNode &startNode, NetlistNode &endNode) {
    TraversalMap traversalMap;
    Visitor visitor(netlist, traversalMap);
    DepthFirstSearch dfs(visitor, startNode);
    return buildPath(traversalMap, startNode, endNode);
  }

private:
  Netlist &netlist;
};

} // End namespace netlist.
