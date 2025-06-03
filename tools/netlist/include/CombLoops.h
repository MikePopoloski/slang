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
        using CycleType = CycleDetectorType::CycleType;

        CycleDetectorType detector(netlist);
        auto result = detector.detectCycles();

        // Canonicalise the result by sorting by node ID.
        std::sort(result.begin(), result.end(), [](CycleType const& a, CycleType const& b) {
            for (size_t i = 0; i < std::min(a.size(), b.size()); i++) {
                if (a[i]->ID != b[i]->ID) {
                    return a[i]->ID < b[i]->ID;
                }
            }
            return false;
        });

        return result;
    }
};

} // namespace netlist
