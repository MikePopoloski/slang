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
#include "fmt/color.h"
#include "fmt/format.h"
#include <iostream>

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Expression.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/util/Util.h"

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

/// Base class representing various selectors that can be applied to references
/// to structured variables (eg vectors, structs, unions).
struct VariableSelectorBase {
    VariableSelectorKind kind;
    explicit VariableSelectorBase(VariableSelectorKind kind) : kind(kind) {}
    virtual ~VariableSelectorBase() = default;
    virtual std::string toString() const = 0;

    bool isElementSelect() const { return kind == VariableSelectorKind::ElementSelect; }
    bool isRangeSelect() const { return kind == VariableSelectorKind::RangeSelect; }
    bool isMemberAccess() const { return kind == VariableSelectorKind::MemberAccess; }
    bool isArraySelect() const { return isElementSelect() || isRangeSelect(); }

    template<typename T>
    T& as() {
        SLANG_ASSERT(T::isKind(kind));
        return *(static_cast<T*>(this));
    }

    template<typename T>
    const T& as() const {
        SLANG_ASSERT(T::isKind(kind));
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

    int32_t getIndexInt() const {
        auto intValue = index.integer().as<int32_t>();
        SLANG_ASSERT(intValue && "could not convert index to int32_t");
        return *intValue;
    }

    std::string toString() const override { return fmt::format("[{}]", index.toString()); }
};

/// A variable selector representing a range selector.
struct VariableRangeSelect : public VariableSelectorBase {
    ConstantValue leftIndex, rightIndex;
    ast::RangeSelectionKind selectionKind;

    VariableRangeSelect(ConstantValue leftIndex, ConstantValue rightIndex, ast::RangeSelectionKind selectionKind) :
        VariableSelectorBase(VariableSelectorKind::RangeSelect), leftIndex(std::move(leftIndex)),
        rightIndex(std::move(rightIndex)), selectionKind(selectionKind) {}

    static bool isKind(VariableSelectorKind otherKind) {
        return otherKind == VariableSelectorKind::RangeSelect;
    }

    int32_t getLeftIndexInt() const {
        auto intValue = leftIndex.integer().as<int32_t>();
        SLANG_ASSERT(intValue && "could not convert left index to int32_t");
        return *intValue;
    }

    int32_t getRightIndexInt() const {
        auto intValue = rightIndex.integer().as<int32_t>();
        SLANG_ASSERT(intValue && "could not convert right index to int32_t");
        return *intValue;
    }

    std::string toString() const override {
        return fmt::format("[{}:{}]", leftIndex.toString(), rightIndex.toString());
    }
};

/// A variable selector representing member access of a structure.
struct VariableMemberAccess : public VariableSelectorBase {
    const std::string_view name;

    VariableMemberAccess(const std::string_view name) :
        VariableSelectorBase(VariableSelectorKind::MemberAccess), name(name) {}

    static bool isKind(VariableSelectorKind otherKind) {
        return otherKind == VariableSelectorKind::MemberAccess;
    }

    std::string toString() const override { return fmt::format(".{}", name); }
};

/// A class representing a dependency between two variables in the netlist.
class NetlistEdge : public DirectedEdge<NetlistNode, NetlistEdge> {
public:
    NetlistEdge(NetlistNode& sourceNode, NetlistNode& targetNode) :
        DirectedEdge(sourceNode, targetNode) {}

    void disable() { disabled = true; }

public:
    bool disabled{};
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
        SLANG_ASSERT(T::isKind(kind));
        return *(static_cast<T*>(this));
    }

    template<typename T>
    const T& as() const {
        SLANG_ASSERT(T::isKind(kind));
        return const_cast<T&>(this->as<T>());
    }

    /// Return the out degree of this node, including only enabled edges.
    size_t outDegree() {
        size_t count = 0;
        for (auto& edge : edges) {
            if (!edge->disabled) {
                count++;
            }
        }
        return count;
    }

    std::string_view getName() const { return symbol.name; }

public:
    size_t ID;
    NodeKind kind;
    const ast::Symbol& symbol;

private:
    static size_t nextID;
};

/// A class representing a port declaration.
class NetlistPortDeclaration : public NetlistNode {
public:
    NetlistPortDeclaration(const ast::Symbol& symbol) :
        NetlistNode(NodeKind::PortDeclaration, symbol) {}

    static bool isKind(NodeKind otherKind) { return otherKind == NodeKind::PortDeclaration; }

public:
    std::string hierarchicalPath;
};

/// A class representing a variable declaration.
class NetlistVariableDeclaration : public NetlistNode {
public:
    NetlistVariableDeclaration(const ast::Symbol& symbol) :
        NetlistNode(NodeKind::VariableDeclaration, symbol) {}

    static bool isKind(NodeKind otherKind) { return otherKind == NodeKind::VariableDeclaration; }

public:
    std::string hierarchicalPath;
};

/// A class representing a variable declaration alias.
class NetlistVariableAlias : public NetlistNode {
public:
    NetlistVariableAlias(const ast::Symbol& symbol) :
        NetlistNode(NodeKind::VariableAlias, symbol) {}

    static bool isKind(NodeKind otherKind) { return otherKind == NodeKind::VariableAlias; }

public:
    std::string hierarchicalPath;
};

/// A class representing a variable reference.
class NetlistVariableReference : public NetlistNode {
public:
    using SelectorsListType = std::vector<std::unique_ptr<VariableSelectorBase>>;

    NetlistVariableReference(const ast::Symbol& symbol, const ast::Expression& expr,
                             bool leftOperand) :
        NetlistNode(NodeKind::VariableReference, symbol),
        expression(expr), leftOperand(leftOperand) {}

    void addElementSelect(const ConstantValue& index) {
        selectors.emplace_back(std::make_unique<VariableElementSelect>(index));
    }
    void addRangeSelect(const ConstantValue& leftIndex, const ConstantValue& rightIndex, ast::RangeSelectionKind selectionKind) {
        selectors.emplace_back(std::make_unique<VariableRangeSelect>(leftIndex, rightIndex, selectionKind));
    }
    void addMemberAccess(std::string_view name) {
        selectors.emplace_back(std::make_unique<VariableMemberAccess>(name));
    }

    static bool isKind(NodeKind otherKind) { return otherKind == NodeKind::VariableReference; }

    bool isLeftOperand() const { return leftOperand; }

    /// Return a string representation of the selectors applied to this
    /// variable reference.
    std::string selectorString() const {
        std::string buffer;
        for (auto& selector : selectors) {
            buffer += selector->toString();
        }
        return buffer;
    }

    /// Return a string representation of this variable reference.
    std::string toString() const { return fmt::format("{}{}", getName(), selectorString()); }

public:
    /// The expression containing the variable reference.
    const ast::Expression& expression;
    /// Whether the variable reference is assignd to (ie appearing on the
    /// left-hand side of an assignent), or otherwise read from.
    bool leftOperand;
    /// Selectors applied to the variable reference.
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
        SLANG_ASSERT(lookupPort(nodePtr->hierarchicalPath) == nullptr &&
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
        SLANG_ASSERT(lookupVariable(nodePtr->hierarchicalPath) == nullptr &&
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
                                                   const ast::Expression& expr, bool leftOperand) {
        auto nodePtr = std::make_unique<NetlistVariableReference>(symbol, expr, leftOperand);
        auto& node = nodePtr->as<NetlistVariableReference>();
        nodes.push_back(std::move(nodePtr));
        DEBUG_PRINT("Add var ref " << symbol.name << "\n");
        return node;
    }

    /// Find a port declaration node in the netlist by hierarchical path.
    NetlistPortDeclaration* lookupPort(std::string_view hierarchicalPath) {
        auto compareNode = [&hierarchicalPath](const std::unique_ptr<NetlistNode>& node) {
            return node->kind == NodeKind::PortDeclaration &&
                   node->as<NetlistPortDeclaration>().hierarchicalPath == hierarchicalPath;
        };
        auto it = std::ranges::find_if(*this, compareNode);
        return it != end() ? &it->get()->as<NetlistPortDeclaration>() : nullptr;
    }

    /// Find a variable declaration node in the netlist by hierarchical path.
    /// Note that this does not lookup alias nodes.
    NetlistVariableDeclaration* lookupVariable(std::string_view hierarchicalPath) {
        auto compareNode = [&hierarchicalPath](const std::unique_ptr<NetlistNode>& node) {
            return node->kind == NodeKind::VariableDeclaration &&
                   node->as<NetlistVariableDeclaration>().hierarchicalPath == hierarchicalPath;
        };
        auto it = std::ranges::find_if(*this, compareNode);
        return it != end() ? &it->get()->as<NetlistVariableDeclaration>() : nullptr;
    }

    /// Find a variable reference node in the netlist by its syntax.
    /// Note that this does not include the hierarchical path, which is only
    /// associated with the corresponding variable declaration nodes.
    NetlistVariableReference* lookupVariableReference(std::string_view syntax) {
        auto compareNode = [&syntax](const std::unique_ptr<NetlistNode>& node) {
            return node->kind == NodeKind::VariableReference &&
                   node->as<NetlistVariableReference>().toString() == syntax;
        };
        auto it = std::ranges::find_if(*this, compareNode);
        return it != end() ? &it->get()->as<NetlistVariableReference>() : nullptr;
    }
};

} // namespace netlist
