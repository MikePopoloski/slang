#pragma once

#include <algorithm>
#include <vector>

namespace netlist {

class NetlistNode;

class NetlistPath {
  std::vector<const NetlistNode*> nodes;

public:
  NetlistPath() = default;

  NetlistPath(std::vector<const NetlistNode*> nodes) : nodes(std::move(nodes)) {};

  void add(const NetlistNode &node) {
    nodes.push_back(&node);
  }

  void add(const NetlistNode *node) {
    nodes.push_back(node);
  }

  void reverse() {
    std::reverse(nodes.begin(), nodes.end());
  }

  bool empty() const { return nodes.empty(); }
};

} // End namespace netlist.
