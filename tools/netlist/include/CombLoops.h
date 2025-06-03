//------------------------------------------------------------------------------
//! @file CombLoops.h
//! @brief Algorithm for finding combinatorial loops
//
// SPDX-FileCopyrightText: Udi Finkelstein
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "CycleDetector.h"
#include "Netlist.h"
#include <algorithm>

namespace netlist {

struct CombEdgePredicate {
    CombEdgePredicate() = default;
    bool operator()(const NetlistEdge& edge) {
        return !edge.disabled && edge.edgeKind == ast::EdgeKind::None;
    }
};

class CombLoops {
    Netlist const& netlist;

public:
    CombLoops(Netlist const& netlist) : netlist(netlist) {}

    auto getAllLoops() {
        using CycleDetectorType = CycleDetector<NetlistNode, NetlistEdge, CombEdgePredicate>;
        CycleDetectorType detector(netlist);
        return detector.detectCycles();
    }
};

} // namespace netlist
