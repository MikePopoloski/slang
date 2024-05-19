#pragma once

#include <unordered_map>
#include <stack>
#include <optional>

using namespace slang;

using namespace netlist {

/// Map names to NetlistNodes. Maintain a reference to a parent table, to which
/// lookups can be deferred if they cannot be resolved in the current symbol
/// table.
class SymbolTable {
public:
    using SymbolMap = std::unordered_map<std::string, NetlistNode*>;

    explicit SymbolTable(std::shared_ptr<SymbolTable> parent) : parent(parent) {}

    auto insert(std::string const &name, NetlistNode *node) {
      SLANG_ASSERT(symbols.count(name) == 0 && "symbol already exists");
      symbols[name] = node;
    }

    std::optional<std::string> lookup(std::string const&name) {
      if (symbols.find(name) != symbols.end()) {
        return symbols[name];
      } else if (parent) {
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

  auto pushScope() {
    scoped.emplace(std::make_shared<SymbolTable>(currentScope());
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

  std::optional<std::string> lookup(std::string const&name) {
    return currentScope()->lookup(name);
  }

private:
  SymTabPtr currentScope() const { return scopes.top(); }
  std::stack<SymTabPtr> scopes;
};

}
