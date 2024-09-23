// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Netlist.h"
#include "PathFinder.h"
#include "visitors/NetlistVisitor.h"
#include <string>

#include "slang/ast/Compilation.h"

using namespace netlist;

inline Netlist createNetlist(ast::Compilation& compilation) {
    Netlist netlist;
    NetlistVisitorOptions options;
    NetlistVisitor visitor(compilation, netlist, options);
    compilation.getRoot().visit(visitor);
    netlist.split();
    return netlist;
}

inline Netlist createNetlist(ast::Compilation& compilation, NetlistVisitorOptions const& options) {
    Netlist netlist;
    NetlistVisitor visitor(compilation, netlist, options);
    compilation.getRoot().visit(visitor);
    netlist.split();
    return netlist;
}

inline bool pathExists(Netlist& netlist, const std::string& startName, const std::string& endName) {
    PathFinder pathFinder(netlist);
    auto* startNode = netlist.lookupPort(startName);
    auto* endNode = netlist.lookupPort(endName);
    return !pathFinder.find(*startNode, *endNode).empty();
}
