#pragma once

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
};

} // End namespace netlist.
