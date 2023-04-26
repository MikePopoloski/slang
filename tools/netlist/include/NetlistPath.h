#pragma once

#include <vector>

namespace slang {

class NetlistNode;

class NetlistPath {
  std::vector<const NetlistNode*> nodes;

public:
  NetlistPath() = default;
};

} // End namespace slang.
