#pragma once

#include <deque>
#include <unordered_map>
#include <stack>
#include <deque>
#include <optional>
#include <string>
#include <memory>

#include "Netlist.h"

using namespace slang;

namespace netlist {

/// Hold a stack of symbols and their corresponding netlist nodes that
/// represents the order of assignments within a procedural block. Provide a
/// lookup function that matches the name and whether the two assignments are
/// overlapping. Use a deque container to allow lookups.
class SymbolStack {
public:
    SymbolStack() = default;
    SymbolStack(std::shared_ptr<SymbolStack> &parent) : parent(parent) {}

    auto push(std::string const& name, NetlistVariableReference* node) { symbols.emplace_back(name, node); }

    std::optional<NetlistVariableReference*> lookup(std::string const&name, ConstantRange const&bounds) {
        auto it = std::find_if(symbols.begin(), symbols.end(),
                               [&](std::pair<std::string, NetlistVariableReference*> const& s) {
                                   return s.first == name && s.second->bounds.overlaps(bounds);
                               });
        if (it != symbols.end()) {
            return it->second;
        }
        else if (parent.get() != nullptr) {
            return parent->lookup(name, bounds);
        }
        return std::nullopt;
    }

private:
  std::deque<std::pair<std::string, NetlistVariableReference*>> symbols;
  std::shared_ptr<SymbolStack> parent;
};

/// Add scoping to SymbolStack lookups by maintaining a stack of tables.
class ScopedSymbolStack {
  using SymTabPtr = std::shared_ptr<SymbolStack>;

public:
  explicit ScopedSymbolStack() { pushScope(); }

  void pushScope() {
    scopes.push(std::make_shared<SymbolStack>());
  }

  auto popScope() {
    if (scopes.size() > 1) {
      scopes.pop();
    } else {
      SLANG_THROW(std::runtime_error("cannot pop the global scope"));
    }
  }

  auto push(std::string const &name, NetlistVariableReference *node) {
    return currentScope()->push(name, node);
  }

  std::optional<NetlistVariableReference*> lookup(std::string const&name, ConstantRange const&bounds) {
    return currentScope()->lookup(name, bounds);
  }

private:
  SymTabPtr const &currentScope() const { return scopes.top(); }
  std::stack<SymTabPtr> scopes;
};

}
