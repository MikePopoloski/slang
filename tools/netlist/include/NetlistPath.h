#pragma once

#include <algorithm>
#include <vector>

namespace netlist {

class NetlistNode;

class NetlistPath {
public:
  using NodeListType = std::vector<const NetlistNode*>;
  using iterator = typename NodeListType::iterator;
  using const_iterator = typename NodeListType::const_iterator;

  NetlistPath() = default;

  NetlistPath(NodeListType nodes) : nodes(std::move(nodes)) {};

  const_iterator begin() const { return nodes.begin(); }
  const_iterator end() const { return nodes.end(); }
  iterator begin() { return nodes.begin(); }
  iterator end() { return nodes.end(); }

  void add(const NetlistNode &node) {
    nodes.push_back(&node);
  }

  void add(const NetlistNode *node) {
    nodes.push_back(node);
  }

  void reverse() {
    std::reverse(nodes.begin(), nodes.end());
  }

  size_t size() const { return nodes.size(); }
  bool empty() const { return nodes.empty(); }

private:
  NodeListType nodes;
};

} // End namespace netlist.
