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
#include <utility>
#include <vector>

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Expression.h"
#include "slang/ast/Symbol.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/numeric/SVInt.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/util/Util.h"

using namespace slang;

template<>
class fmt::formatter<ConstantRange> {
public:
    constexpr auto parse(format_parse_context& ctx) { return ctx.begin(); }
    template<typename Context>
    constexpr auto format(ConstantRange const& range, Context& ctx) const {
        return format_to(ctx.out(), "[{}:{}]", range.upper(), range.lower());
    }
};

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

static std::string getSymbolHierPath(const ast::Symbol& symbol) {

    // Resolve the hierarchical path of the symbol.
    std::string buffer;
    symbol.getHierarchicalPath(buffer);

    return buffer;
}

static std::string resolveSymbolHierPath(const ast::Symbol& symbol) {

    // Resolve the hierarchical path of the symbol.
    std::string buffer;
    symbol.getHierarchicalPath(buffer);

    // Is the symbol is a modport, use the modport name to adjust the
    // hierachical path to match the corresponding variable declaration in the
    // interface.
    if (symbol.kind == ast::SymbolKind::ModportPort) {
        auto const& modportSymbol = symbol.getParentScope()->asSymbol();
        auto& modportName = modportSymbol.name;
        auto oldSuffix = fmt::format(".{}.{}", modportSymbol.name, symbol.name);
        auto newSuffix = fmt::format(".{}", symbol.name);
        DEBUG_PRINT("hierPath={}, oldSuffix={}, newSuffix={}\n", buffer, oldSuffix, newSuffix);
        SLANG_ASSERT(buffer.ends_with(oldSuffix));
        buffer.replace(buffer.end() - (ptrdiff_t)oldSuffix.length(), buffer.end(),
                       newSuffix.begin(), newSuffix.end());
    }

    return buffer;
}

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
    const ast::Expression& expr;
    ConstantValue index;

    VariableElementSelect(ast::Expression const& expr, ConstantValue index) :
        VariableSelectorBase(VariableSelectorKind::ElementSelect), expr(expr),
        index(std::move(index)) {}

    static bool isKind(VariableSelectorKind otherKind) {
        return otherKind == VariableSelectorKind::ElementSelect;
    }

    bool indexIsConstant() const { return !index.bad(); }

    int32_t getIndexInt() const {
        auto intValue = index.integer().as<int32_t>();
        SLANG_ASSERT(intValue && "could not convert index to int32_t");
        return *intValue;
    }

    std::string toString() const override {
        if (indexIsConstant()) {
            return fmt::format("[{}]", index.toString());
        }
        else {
            return fmt::format("[{}]", expr.syntax->toString());
        }
    }
};

/// A variable selector representing a range selector.
struct VariableRangeSelect : public VariableSelectorBase {
    const ast::RangeSelectExpression& expr;
    ConstantValue leftIndex, rightIndex;

    VariableRangeSelect(ast::RangeSelectExpression const& expr, ConstantValue leftIndex,
                        ConstantValue rightIndex) :
        VariableSelectorBase(VariableSelectorKind::RangeSelect), expr(expr),
        leftIndex(std::move(leftIndex)), rightIndex(std::move(rightIndex)) {}

    static bool isKind(VariableSelectorKind otherKind) {
        return otherKind == VariableSelectorKind::RangeSelect;
    }

    bool leftIndexIsConstant() const { return !leftIndex.bad(); }

    bool rightIndexIsConstant() const { return !rightIndex.bad(); }

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
        std::string left;
        if (leftIndexIsConstant()) {
            left = leftIndex.toString();
        }
        else {
            left = expr.left().syntax->toString();
        }
        std::string right;
        if (rightIndexIsConstant()) {
            right = rightIndex.toString();
        }
        else {
            right = expr.right().syntax->toString();
        }
        switch (expr.getSelectionKind()) {
            case ast::RangeSelectionKind::Simple:
                return fmt::format("[{}:{}]", left, right);
            case ast::RangeSelectionKind::IndexedUp:
                return fmt::format("[{}+:{}]", left, right);
            case ast::RangeSelectionKind::IndexedDown:
                return fmt::format("[{}-:{}]", left, right);
            default:
                SLANG_UNREACHABLE;
        }
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
        ID(++nextID), kind(kind), symbol(symbol), edgeKind(ast::EdgeKind::None) {};
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
    ast::EdgeKind edgeKind;
    bool blocked{};

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

/// A class representing a variable declaration alias.
class NetlistVariableAlias : public NetlistNode {
public:
    NetlistVariableAlias(const ast::Symbol& symbol, ConstantRange overlap) :
        NetlistNode(NodeKind::VariableAlias, symbol), overlap(overlap) {}

    static bool isKind(NodeKind otherKind) { return otherKind == NodeKind::VariableAlias; }

public:
    std::string hierarchicalPath;
    ConstantRange overlap;
};

/// A class representing a variable declaration.
class NetlistVariableDeclaration : public NetlistNode {
public:
    NetlistVariableDeclaration(const ast::Symbol& symbol) :
        NetlistNode(NodeKind::VariableDeclaration, symbol) {}

    static bool isKind(NodeKind otherKind) { return otherKind == NodeKind::VariableDeclaration; }

    void addAlias(NetlistVariableAlias* node) { aliases.push_back(node); }

public:
    std::string hierarchicalPath;
    std::vector<NetlistVariableAlias*> aliases;
};

/// A class representing a variable reference.
class NetlistVariableReference : public NetlistNode {
public:
    using SelectorsListType = std::vector<std::unique_ptr<VariableSelectorBase>>;

    NetlistVariableReference(const ast::Symbol& symbol, const ast::Expression& expr,
                             bool leftOperand) :
        NetlistNode(NodeKind::VariableReference, symbol), expression(expr),
        leftOperand(leftOperand) {}

    void addElementSelect(ast::ElementSelectExpression const& expr, const ConstantValue& index) {
        selectors.emplace_back(std::make_unique<VariableElementSelect>(expr.selector(), index));
    }

    void addRangeSelect(ast::RangeSelectExpression const& expr, const ConstantValue& leftIndex,
                        const ConstantValue& rightIndex) {
        selectors.emplace_back(std::make_unique<VariableRangeSelect>(expr, leftIndex, rightIndex));
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

    /// Return a string of the syntax for this variable reference.
    std::string syntax() const {
        if (selectors.empty()) {
            return fmt::format("{}", getName());
        }
        else {
            return fmt::format("{}{}", getName(), selectorString());
        }
    }

    /// Return a string representation of this variable reference with the name
    /// and access bounds.
    std::string toString() const {
        return fmt::format("{}[{}:{}]", getName(), bounds.upper(), bounds.lower());
    }

public:
    /// The expression containing the variable reference.
    const ast::Expression& expression;
    /// Whether the variable reference is assignd to (ie appearing on the
    /// left-hand side of an assignent), or otherwise read from.
    bool leftOperand;
    /// Selectors applied to the variable reference.
    SelectorsListType selectors;
    // Access bounds.
    ConstantRange bounds;
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
        DEBUG_PRINT("New node: port declaration {}\n", node.hierarchicalPath);
        return node;
    }

    /// Add a variable declaration node to the netlist.
    NetlistVariableDeclaration& addVariableDeclaration(const ast::Symbol& symbol) {
        std::string hierPath = getSymbolHierPath(symbol);
        if (auto* result = lookupVariable(hierPath)) {
            DEBUG_PRINT("Variable declaration for {} already exists", hierPath);
            return *result;
        }
        else {
            auto nodePtr = std::make_unique<NetlistVariableDeclaration>(symbol);
            nodePtr->hierarchicalPath = hierPath;
            auto& node = nodePtr->as<NetlistVariableDeclaration>();
            nodes.push_back(std::move(nodePtr));
            DEBUG_PRINT("Add var decl {}\n", node.hierarchicalPath);
            return node;
        }
    }

    /// Add a variable declaration alias node to the netlist.
    NetlistVariableAlias& addVariableAlias(const ast::Symbol& symbol, ConstantRange overlap) {
        auto nodePtr = std::make_unique<NetlistVariableAlias>(symbol, overlap);
        auto& node = nodePtr->as<NetlistVariableAlias>();
        symbol.getHierarchicalPath(node.hierarchicalPath);
        nodes.push_back(std::move(nodePtr));
        DEBUG_PRINT("New node: variable alias {}\n", node.hierarchicalPath);
        return node;
    }

    /// Add a variable reference node to the netlist.
    NetlistVariableReference& addVariableReference(const ast::Symbol& symbol,
                                                   const ast::Expression& expr, bool leftOperand) {
        auto nodePtr = std::make_unique<NetlistVariableReference>(symbol, expr, leftOperand);
        auto& node = nodePtr->as<NetlistVariableReference>();
        nodes.push_back(std::move(nodePtr));
        DEBUG_PRINT("New node: variable reference {}\n", symbol.name);
        return node;
    }

    // without this, the base class method will be hidden,
    // even when calling netlist.addEdge with only 2 parameters
    using DirectedGraph<NetlistNode, NetlistEdge>::addEdge;

    NetlistEdge& addEdge(NetlistNode& sourceNode, NetlistNode& targetNode, ast::EdgeKind edgeKind) {
        auto& edge = DirectedGraph<NetlistNode, NetlistEdge>::addEdge(sourceNode, targetNode);
        targetNode.edgeKind = edgeKind;
        return edge;
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
                   node->as<NetlistVariableReference>().syntax() == syntax;
        };
        auto it = std::ranges::find_if(*this, compareNode);
        return it != end() ? &it->get()->as<NetlistVariableReference>() : nullptr;
    }

    struct VarSplit {
        NetlistVariableDeclaration* varDecl;
        ConstantRange bounds;
        NetlistEdge* inEdge;
        std::vector<NetlistEdge*> outEdges;
    };

    // A list of modifications to apply to the netlist.
    using SplittingList = std::vector<VarSplit>;

    /// Identify the new ALIAS nodes and their edges to add to the netlist.
    void identifySplits(SplittingList& mods) {
        for (auto& node : nodes) {

            // Find variable declaration nodes in the graph that have multiple
            // outgoing edges.
            if (node->kind == NodeKind::VariableDeclaration && node->outDegree() > 1) {
                auto& varDeclNode = node->as<NetlistVariableDeclaration>();
                auto& varType = varDeclNode.symbol.getDeclaredType()->getType();
                DEBUG_PRINT("Variable {} has type {}\n", varDeclNode.hierarchicalPath,
                            varType.toString());

                // Create a list of incoming edges to the declration node.
                std::vector<NetlistEdge*> inEdges;
                getInEdgesToNode(*node, inEdges);

                // For each in edge (assignment to a part of the variable),
                // make a list of the out edges with bounds that intersect the
                // in edge's bounds.
                for (auto* inEdge : inEdges) {
                    if (inEdge->getSourceNode().kind != NodeKind::VariableReference) {
                        continue;
                    }

                    auto& sourceVarRef = inEdge->getSourceNode().as<NetlistVariableReference>();

                    std::vector<NetlistEdge*> outEdges;

                    for (auto& outEdge : *node) {
                        if (outEdge->getTargetNode().kind != NodeKind::VariableReference) {
                            continue;
                        }

                        auto& targetVarRef =
                            outEdge->getTargetNode().as<NetlistVariableReference>();

                        // Match if the selection made by the target node intersects with the
                        // selection made by the source node.
                        if (sourceVarRef.bounds.overlaps(targetVarRef.bounds)) {
                            auto overlap = sourceVarRef.bounds.intersect(targetVarRef.bounds);
                            DEBUG_PRINT("New split path: REF {} -> ALIAS {}[{}:{}] -> REF {}\n",
                                        sourceVarRef.toString(), varDeclNode.hierarchicalPath,
                                        overlap.upper(), overlap.lower(), targetVarRef.toString());
                            outEdges.push_back(outEdge.get());
                        }
                    }
                    mods.push_back({&varDeclNode, sourceVarRef.bounds, inEdge, outEdges});
                }
            }
        }
    }

    // Apply the splitting operations to the netlist graph.
    void applySplits(SplittingList& mods) {
        for (auto& mod : mods) {

            // Disable the existing edges.
            mod.inEdge->disable();
            for (auto* outEdge : mod.outEdges) {
                outEdge->disable();
            }

            // Create a new node that aliases the variable declaration.
            auto& varAliasNode = addVariableAlias(mod.varDecl->symbol, mod.bounds);

            // Record the alias on the orginal declaration.
            mod.varDecl->addAlias(&varAliasNode);

            // Create the in edge to the new node.
            mod.inEdge->getSourceNode().addEdge(varAliasNode);

            // Create the out edges.
            for (auto* outEdge : mod.outEdges) {
                varAliasNode.addEdge(outEdge->getTargetNode());
            }
        }
    }

    /// Perform a transformation on the netlist graph to split variable
    /// declaration nodes into multiple parts corresponding to the access ranges
    /// of references for incoming source variables to outdgoing target
    /// variables. For each new split of the variable declration, create an ALIAS
    /// node. For example, given a path of the form:
    ///
    ///   var ref a ---> var decl x ---> var ref b
    ///
    /// If a and b reference the same part of x, then transform the path and
    /// mark the original edges as disabled:
    ///
    ///   var ref a -x-> var alias x -x-> var ref b
    ///   var ref a ---> var alias x ---> var ref
    ///
    void split() {
        SplittingList mods;
        identifySplits(mods);
        applySplits(mods);
    }
};

} // namespace netlist
