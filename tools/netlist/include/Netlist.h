//------------------------------------------------------------------------------
//! @file Netlist.h
//! @brief A class that represents the netlist of an AST.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "fmt/color.h"
#include "fmt/format.h"
#include <iostream>

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"

#include "Config.h"
#include "Debug.h"
#include "DirectedGraph.h"
#include "NetlistPath.h"

namespace slang {

class NetlistNode;
class NetlistEdge;

enum class NodeKind {
  None = 0,
  PortDeclaration,
  VariableDeclaration,
  VariableReference
};

enum class VariableSelectorKind {
  ElementSelect,
  RangeSelect,
  MemberAccess
};

struct VariableSelectorBase {
  VariableSelectorKind kind;
  explicit VariableSelectorBase(VariableSelectorKind kind) : kind(kind) {}
  virtual ~VariableSelectorBase() = default;
  virtual std::string toString() const = 0;
};

/// A variable selector representing an element selector.
struct VariableElementSelect : public VariableSelectorBase {
  ConstantValue index;
  VariableElementSelect(ConstantValue index) :
    VariableSelectorBase(VariableSelectorKind::ElementSelect), index(std::move(index)) {}
  std::string toString() const override {
    return fmt::format("[%s]", index.toString());
  }
};

/// A variable selector representing a range selector.
struct VariableRangeSelect : public VariableSelectorBase {
  ConstantValue leftIndex, rightIndex;
  VariableRangeSelect(ConstantValue leftIndex, ConstantValue rightIndex) :
    VariableSelectorBase(VariableSelectorKind::RangeSelect),
    leftIndex(std::move(leftIndex)), rightIndex(std::move(rightIndex)) {}
  std::string toString() const override {
    return fmt::format("[%s:%s]", leftIndex.toString(), rightIndex.toString());
  }
};

/// A variable selector representing member access of a structure.
struct VariableMemberAccess : public VariableSelectorBase {
  std::string_view name;
  VariableMemberAccess(std::string_view name) :
    VariableSelectorBase(VariableSelectorKind::MemberAccess), name(name) {}
  std::string toString() const override {
    return fmt::format(".%s", name);
  }
};

/// A class representing a node in the netlist, corresponding to the appearance
/// of a variable symbol, with zero or more selectors applied.
class NetlistNode : public Node<NetlistNode, NetlistEdge> {
public:
  NetlistNode(NodeKind kind, const ast::Symbol &symbol) :
    ID(++nextID), kind(kind), symbol(symbol) {};
   ~NetlistNode() override = default;

  template<typename T>
  T& as() {
    assert(T::isKind(kind));
    return *(dynamic_cast<T*>(this));
  }

  template<typename T>
  const T& as() const {
    assert(T::isKind(kind));
    return const_cast<T&>(this->as<T>());
  }

  std::string_view getName() const { return symbol.name; }
  virtual std::string toString() const = 0;

public:
  size_t ID;
  NodeKind kind;
  const ast::Symbol &symbol;

private:
  static size_t nextID;
  std::vector<std::unique_ptr<VariableSelectorBase>> selectors;
};

size_t NetlistNode::nextID = 0;

/// A class representing a dependency between two variables in the netlist.
class NetlistEdge : public DirectedEdge<NetlistNode, NetlistEdge> {
public:
  NetlistEdge(NetlistNode &targetNode) : DirectedEdge(targetNode) {}
};

/// A class representing a port declaration.
class NetlistPortDeclaration : public NetlistNode {
public:
  NetlistPortDeclaration(const ast::Symbol &symbol) :
    NetlistNode(NodeKind::PortDeclaration, symbol) {}

  static bool isKind(NodeKind otherKind) {
    return otherKind == NodeKind::PortDeclaration;
  }

  std::string toString() const override {
    return fmt::format("port {}", symbol.name);
  }

public:
  std::string hierarchicalPath;
};

/// A class representing a variable declaration.
class NetlistVariableDeclaration : public NetlistNode {
public:
  NetlistVariableDeclaration(const ast::Symbol &symbol) :
    NetlistNode(NodeKind::VariableDeclaration, symbol) {}

  static bool isKind(NodeKind otherKind) {
    return otherKind == NodeKind::VariableDeclaration;
  }

  std::string toString() const override {
    return fmt::format("var {}", symbol.name);
  }

public:
  std::string hierarchicalPath;
};

/// A class representing a variable reference.
class NetlistVariableReference : public NetlistNode {
public:
  NetlistVariableReference(const ast::Symbol &symbol) :
    NetlistNode(NodeKind::VariableReference, symbol) {}

  void addElementSelect(const ConstantValue &index) {
    selectors.emplace_back(std::make_unique<VariableElementSelect>(index));
  }
  void addRangeSelect(const ConstantValue &leftIndex, const ConstantValue &rightIndex) {
    selectors.emplace_back(std::make_unique<VariableRangeSelect>(leftIndex, rightIndex));
  }
  void addMemberAccess(std::string_view name) {
    selectors.emplace_back(std::make_unique<VariableMemberAccess>(name));
  }

  static bool isKind(NodeKind otherKind) {
    return otherKind == NodeKind::VariableReference;
  }

  std::string toString() const override {
    std::string buffer;
    for (auto &selector : selectors) {
      buffer += selector->toString();
    }
    return fmt::format("{}{}", symbol.name, buffer);
  }

private:
  std::vector<std::unique_ptr<VariableSelectorBase>> selectors;
};

/// A class representing the design netlist.
class Netlist : public DirectedGraph<NetlistNode, NetlistEdge> {
public:
  Netlist() : DirectedGraph() {}

  /// Add a port declaration node to the netlist.
  NetlistPortDeclaration &addPortDeclaration(const ast::Symbol &symbol) {
    DEBUG_PRINT("Add port decl " << symbol.name << "\n");
    auto nodePtr = std::make_unique<NetlistPortDeclaration>(symbol);
    auto &node = nodePtr->as<NetlistPortDeclaration>();
    symbol.getHierarchicalPath(node.hierarchicalPath);
    assert(lookupPort(nodePtr->hierarchicalPath) == nullptr && "Port declaration already exists");
    nodes.push_back(std::move(nodePtr));
    return node;
  }

  /// Add a variable declaration node to the netlist.
  NetlistVariableDeclaration &addVariableDeclaration(const ast::Symbol &symbol) {
    DEBUG_PRINT("Add var decl " << symbol.name << "\n");
    auto nodePtr = std::make_unique<NetlistVariableDeclaration>(symbol);
    auto &node = nodePtr->as<NetlistVariableDeclaration>();
    symbol.getHierarchicalPath(node.hierarchicalPath);
    assert(lookupVariable(nodePtr->hierarchicalPath) == nullptr && "Variable declaration already exists");
    nodes.push_back(std::move(nodePtr));
    return node;
  }

  /// Add a variable reference node to the netlist.
  NetlistVariableReference &addVariableReference(const ast::Symbol &symbol) {
    DEBUG_PRINT("Add var ref " << symbol.name << "\n");
    auto nodePtr = std::make_unique<NetlistVariableReference>(symbol);
    auto &node = nodePtr->as<NetlistVariableReference>();
    nodes.push_back(std::move(nodePtr));
    return node;
  }

  /// Find a variable declaration node in the netlist by hierarchical path.
  NetlistNode *lookupVariable(const std::string &hierarchicalPath) {
    auto compareNode = [&hierarchicalPath](const std::unique_ptr<NetlistNode> &node) {
                          return node->kind == NodeKind::VariableDeclaration &&
                                 node->as<NetlistVariableDeclaration>().hierarchicalPath == hierarchicalPath;
                       };
    auto it = std::find_if(begin(), end(), compareNode);
    return it != end() ? it->get() : nullptr;
  }

  /// Find a port declaration node in the netlist by hierarchical path.
  NetlistNode *lookupPort(const std::string &hierarchicalPath) {
    auto compareNode = [&hierarchicalPath](const std::unique_ptr<NetlistNode> &node) {
                          return node->kind == NodeKind::PortDeclaration &&
                                 node->as<NetlistPortDeclaration>().hierarchicalPath == hierarchicalPath;
                       };
    auto it = std::find_if(begin(), end(), compareNode);
    return it != end() ? it->get() : nullptr;
  }

  NetlistPath findPath(NetlistNode &startNode, NetlistNode &endNode) {
    return NetlistPath();
  }
};

} // End namespace slang.

