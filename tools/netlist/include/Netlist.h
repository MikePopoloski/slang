//------------------------------------------------------------------------------
//! @file Netlist.h
//! @brief A class that represents the netlist of an AST.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "Config.h"
#include "Debug.h"
#include "DirectedGraph.h"
#include "NetlistPath.h"
#include "fmt/color.h"
#include "fmt/format.h"
#include <iostream>

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"

using namespace slang;

namespace netlist {

class NetlistNode;
class NetlistEdge;

enum class NodeKind {
    None = 0,
    PortDeclaration,
    VariableDeclaration,
    VariableReference,
    VariableAlias
};

enum class VariableSelectorKind { ElementSelect, RangeSelect, MemberAccess };

struct VariableSelectorBase {
    VariableSelectorKind kind;
    explicit VariableSelectorBase(VariableSelectorKind kind) : kind(kind) {}
    virtual ~VariableSelectorBase() = default;
    // virtual bool operator==(const VariableSelectorBase &E) const = 0;
    // virtual bool operator!=(const VariableSelectorBase &E) const = 0;
    virtual std::string toString() const = 0;

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
};

/// A variable selector representing an element selector.
struct VariableElementSelect : public VariableSelectorBase {
    ConstantValue index;

    VariableElementSelect(ConstantValue index) :
        VariableSelectorBase(VariableSelectorKind::ElementSelect), index(std::move(index)) {}

    static bool isKind(VariableSelectorKind otherKind) {
        return otherKind == VariableSelectorKind::ElementSelect;
    }

    size_t getIndexInt() const {
        auto intValue = index.integer().as<size_t>();
        assert(intValue && "could not convert index to size_t");
        return *intValue;
    }

    std::string toString() const override { return fmt::format("[{}]", index.toString()); }
};

/// A variable selector representing a range selector.
struct VariableRangeSelect : public VariableSelectorBase {
    ConstantValue leftIndex, rightIndex;

    VariableRangeSelect(ConstantValue leftIndex, ConstantValue rightIndex) :
        VariableSelectorBase(VariableSelectorKind::RangeSelect), leftIndex(std::move(leftIndex)),
        rightIndex(std::move(rightIndex)) {}

    static bool isKind(VariableSelectorKind otherKind) {
        return otherKind == VariableSelectorKind::RangeSelect;
    }

    size_t getLeftIndexInt() const {
        auto intValue = leftIndex.integer().as<size_t>();
        assert(intValue && "could not convert left index to size_t");
        return *intValue;
    }

    size_t getRightIndexInt() const {
        auto intValue = rightIndex.integer().as<size_t>();
        assert(intValue && "could not convert right index to size_t");
        return *intValue;
    }

    std::string toString() const override {
        return fmt::format("[{}:{}]", leftIndex.toString(), rightIndex.toString());
    }
};

/// A variable selector representing member access of a structure.
struct VariableMemberAccess : public VariableSelectorBase {
    std::string_view name;

    VariableMemberAccess(std::string_view name) :
        VariableSelectorBase(VariableSelectorKind::MemberAccess), name(name) {}

    static bool isKind(VariableSelectorKind otherKind) {
        return otherKind == VariableSelectorKind::MemberAccess;
    }

    std::string toString() const override { return fmt::format(".{}", name); }
};

/// A class representing a node in the netlist, corresponding to the appearance
/// of a variable symbol, with zero or more selectors applied.
class NetlistNode : public Node<NetlistNode, NetlistEdge> {
public:
    NetlistNode(NodeKind kind, const ast::Symbol& symbol) :
        ID(++nextID), kind(kind), symbol(symbol){};
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
    const ast::Symbol& symbol;

private:
    static size_t nextID;
};

size_t NetlistNode::nextID = 0;

/// A class representing a dependency between two variables in the netlist.
class NetlistEdge : public DirectedEdge<NetlistNode, NetlistEdge> {
public:
    NetlistEdge(NetlistNode& sourceNode, NetlistNode& targetNode) :
        DirectedEdge(sourceNode, targetNode) {}

    void disable() { disabled = true; }

public:
    bool disabled{};
};

/// A class representing a port declaration.
class NetlistPortDeclaration : public NetlistNode {
public:
    NetlistPortDeclaration(const ast::Symbol& symbol) :
        NetlistNode(NodeKind::PortDeclaration, symbol) {}

    static bool isKind(NodeKind otherKind) { return otherKind == NodeKind::PortDeclaration; }

    std::string toString() const override { return fmt::format("port {}", hierarchicalPath); }

public:
    std::string hierarchicalPath;
};

/// A class representing a variable declaration.
class NetlistVariableDeclaration : public NetlistNode {
public:
    NetlistVariableDeclaration(const ast::Symbol& symbol) :
        NetlistNode(NodeKind::VariableDeclaration, symbol) {}

    static bool isKind(NodeKind otherKind) { return otherKind == NodeKind::VariableDeclaration; }

    std::string toString() const override { return fmt::format("var {}", hierarchicalPath); }

public:
    std::string hierarchicalPath;
};

/// A class representing a variable declaration alias.
class NetlistVariableAlias : public NetlistNode {
public:
    NetlistVariableAlias(const ast::Symbol& symbol) :
        NetlistNode(NodeKind::VariableAlias, symbol) {}

    static bool isKind(NodeKind otherKind) { return otherKind == NodeKind::VariableAlias; }

    std::string toString() const override { return fmt::format("var alias {}", hierarchicalPath); }

public:
    std::string hierarchicalPath;
};

/// A class representing a variable reference.
class NetlistVariableReference : public NetlistNode {
public:
    using SelectorsListType = std::vector<std::unique_ptr<VariableSelectorBase>>;

    NetlistVariableReference(const ast::Symbol& symbol, const ast::Expression &expr) :
        NetlistNode(NodeKind::VariableReference, symbol), expression(expr) {}

    void addElementSelect(const ConstantValue& index) {
        selectors.emplace_back(std::make_unique<VariableElementSelect>(index));
    }
    void addRangeSelect(const ConstantValue& leftIndex, const ConstantValue& rightIndex) {
        selectors.emplace_back(std::make_unique<VariableRangeSelect>(leftIndex, rightIndex));
    }
    void addMemberAccess(std::string_view name) {
        selectors.emplace_back(std::make_unique<VariableMemberAccess>(name));
    }

    static bool isKind(NodeKind otherKind) { return otherKind == NodeKind::VariableReference; }

    std::string toString() const override {
        std::string buffer;
        for (auto& selector : selectors) {
            buffer += selector->toString();
        }
        return fmt::format("{}{}", symbol.name, buffer);
    }

public:
    const ast::Expression &expression;
    SelectorsListType selectors;
};

/// A class representing the design netlist.
class Netlist : public DirectedGraph<NetlistNode, NetlistEdge> {
public:
    Netlist() : DirectedGraph() {}

    /// Add a port declaration node to the netlist.
    NetlistPortDeclaration& addPortDeclaration(const ast::Symbol& symbol) {
        auto nodePtr = std::make_unique<NetlistPortDeclaration>(symbol);
        auto& node = nodePtr->as<NetlistPortDeclaration>();
        symbol.getHierarchicalPath(node.hierarchicalPath);
        assert(lookupPort(nodePtr->hierarchicalPath) == nullptr &&
               "Port declaration already exists");
        nodes.push_back(std::move(nodePtr));
        DEBUG_PRINT("Add port decl " << node.hierarchicalPath << "\n");
        return node;
    }

    /// Add a variable declaration node to the netlist.
    NetlistVariableDeclaration& addVariableDeclaration(const ast::Symbol& symbol) {
        auto nodePtr = std::make_unique<NetlistVariableDeclaration>(symbol);
        auto& node = nodePtr->as<NetlistVariableDeclaration>();
        symbol.getHierarchicalPath(node.hierarchicalPath);
        assert(lookupVariable(nodePtr->hierarchicalPath) == nullptr &&
               "Variable declaration already exists");
        nodes.push_back(std::move(nodePtr));
        DEBUG_PRINT("Add var decl " << node.hierarchicalPath << "\n");
        return node;
    }

    /// Add a variable declaration alias node to the netlist.
    NetlistVariableAlias& addVariableAlias(const ast::Symbol& symbol) {
        auto nodePtr = std::make_unique<NetlistVariableAlias>(symbol);
        auto& node = nodePtr->as<NetlistVariableAlias>();
        symbol.getHierarchicalPath(node.hierarchicalPath);
        nodes.push_back(std::move(nodePtr));
        DEBUG_PRINT("Add var alias " << node.hierarchicalPath << "\n");
        return node;
    }

    /// Add a variable reference node to the netlist.
    NetlistVariableReference& addVariableReference(const ast::Symbol& symbol,
                                                   const ast::Expression& expr) {
        auto nodePtr = std::make_unique<NetlistVariableReference>(symbol, expr);
        auto& node = nodePtr->as<NetlistVariableReference>();
        nodes.push_back(std::move(nodePtr));
        DEBUG_PRINT("Add var ref " << symbol.name << "\n");
        return node;
    }

    /// Find a variable declaration node in the netlist by hierarchical path.
    /// TODO? Optimise this lookup by maintaining a list of declaration nodes.
    NetlistNode* lookupVariable(const std::string& hierarchicalPath) {
        auto compareNode = [&hierarchicalPath](const std::unique_ptr<NetlistNode>& node) {
            return node->kind == NodeKind::VariableDeclaration &&
                   node->as<NetlistVariableDeclaration>().hierarchicalPath == hierarchicalPath;
        };
        auto it = std::find_if(begin(), end(), compareNode);
        return it != end() ? it->get() : nullptr;
    }

    /// Find a port declaration node in the netlist by hierarchical path.
    /// TODO? Optimise this lookup by maintaining a list of port nodes.
    NetlistNode* lookupPort(const std::string& hierarchicalPath) {
        auto compareNode = [&hierarchicalPath](const std::unique_ptr<NetlistNode>& node) {
            return node->kind == NodeKind::PortDeclaration &&
                   node->as<NetlistPortDeclaration>().hierarchicalPath == hierarchicalPath;
        };
        auto it = std::find_if(begin(), end(), compareNode);
        return it != end() ? it->get() : nullptr;
    }
};

} // namespace netlist
