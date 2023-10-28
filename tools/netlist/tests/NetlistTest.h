// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "Netlist.h"
#include "NetlistVisitor.h"
#include "PathFinder.h"
#include "Test.h"
#include <string>

using namespace netlist;

inline Netlist createNetlist(Compilation& compilation) {
    Netlist netlist;
    NetlistVisitor visitor(compilation, netlist);
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
