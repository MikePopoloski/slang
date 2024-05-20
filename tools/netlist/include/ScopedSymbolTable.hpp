#pragma once

#include <unordered_map>
#include <stack>
#include <optional>
#include <string>
#include <memory>

#include "Netlist.h"

using namespace slang;

namespace netlist {

/// Map names to NetlistNodes. Maintain a reference to a parent table, to which
/// lookups can be deferred if they cannot be resolved in the current symbol
/// table.
class SymbolTable {
public:
    using SymbolMap = std::unordered_map<std::string, NetlistNode*>;

    SymbolTable() = default;
    SymbolTable(std::shared_ptr<SymbolTable> &parent) : parent(parent) {}

    auto insert(std::string const &name, NetlistNode *node) {
      //SLANG_ASSERT(symbols.count(name) == 0 && "symbol already exists");
      symbols[name] = node;
    }

    std::optional<NetlistNode*> lookup(std::string const&name) {
      if (symbols.find(name) != symbols.end()) {
        return symbols[name];
      } else if (parent.get() != nullptr) {
        return parent->lookup(name);
      }
      return std::nullopt;
    }

private:
  SymbolMap symbols;
  std::shared_ptr<SymbolTable> parent;
};

/// Add scoping to SymbolTable lookups by maintaining a stack of tables.
class ScopedSymbolTable {
  using SymTabPtr = std::shared_ptr<SymbolTable>;

public:
  explicit ScopedSymbolTable() { pushScope(); }

  void pushScope() {
    scopes.push(std::make_shared<SymbolTable>());
  }

  auto popScope() {
    if (scopes.size() > 1) {
      scopes.pop();
    } else {
      SLANG_THROW(std::runtime_error("cannot pop the global scope"));
    }
  }

  auto insert(std::string const &name, NetlistNode *node) {
    return currentScope()->insert(name, node);
  }

  std::optional<NetlistNode*> lookup(std::string const&name) {
    return currentScope()->lookup(name);
  }

private:
  SymTabPtr const &currentScope() const { return scopes.top(); }
  std::stack<SymTabPtr> scopes;
};

}
