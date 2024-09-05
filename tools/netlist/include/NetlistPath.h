//------------------------------------------------------------------------------
//! @file NetlistPath.h
//! @brief A class that represents a path within a netlist.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "Netlist.h"
#include <algorithm>
#include <vector>

namespace netlist {

/// A class represening a path traversing nodes in the netlist.
class NetlistPath {
public:
    using NodeListType = std::vector<NetlistNode*>;
    using iterator = typename NodeListType::iterator;
    using const_iterator = typename NodeListType::const_iterator;

    NetlistPath() = default;

    NetlistPath(NodeListType nodes) : nodes(std::move(nodes)) {};

    const_iterator begin() const { return nodes.begin(); }
    const_iterator end() const { return nodes.end(); }
    iterator begin() { return nodes.begin(); }
    iterator end() { return nodes.end(); }

    void add(NetlistNode& node) { nodes.push_back(&node); }

    void add(NetlistNode* node) { nodes.push_back(node); }

    void reverse() { std::ranges::reverse(nodes); }

    size_t size() const { return nodes.size(); }

    bool empty() const { return nodes.empty(); }
    void clear() { nodes.clear(); }

    static std::string getSymbolHierPath(const ast::Symbol& symbol) {
        std::string buffer;
        symbol.getHierarchicalPath(buffer);
        return buffer;
    }

    /// Return index within the path if a variable reference matches the
    /// specified syntax (ie including the hierarchical reference to the
    /// variable name and selectors) and appears on the left-hand side of an
    /// assignment (ie a target).
    std::optional<size_t> findVariable(std::string syntax) {
        auto match = [this, &syntax](NetlistNode* node) {
            if (node->kind == NodeKind::VariableReference) {
                auto& varRefNode = node->as<NetlistVariableReference>();
                auto hierPath = getSymbolHierPath(varRefNode.symbol);
                auto selectorString = varRefNode.selectorString();
                return hierPath + selectorString == syntax;
            }
            else {
                return false;
            }
        };
        auto it = std::ranges::find_if(nodes, match);
        if (it != nodes.end()) {
            return std::make_optional(it - nodes.begin());
        }
        else {
            return std::nullopt;
        }
    }

private:
    NodeListType nodes;
};

} // namespace netlist
