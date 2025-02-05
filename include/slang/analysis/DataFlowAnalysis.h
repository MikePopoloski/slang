//------------------------------------------------------------------------------
//! @file DataFlowAnalysis.h
//! @brief Data flow analysis pass
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/analysis/AbstractFlowAnalysis.h"
#include "slang/analysis/AnalysisContext.h"
#include "slang/util/IntervalMap.h"
#include "slang/util/SmallVector.h"

namespace slang::analysis {

struct DataFlowState {
    // Each tracked variable has its assigned intervals stored here.
    // This should be 64 bytes per variable.
    SmallVector<AssignedBitsMap, 2> assigned;

    DataFlowState() = default;
    DataFlowState(DataFlowState&& other) = default;
    DataFlowState& operator=(DataFlowState&& other) = default;
};

class DataFlowAnalysis : public AbstractFlowAnalysis<DataFlowAnalysis, DataFlowState> {
public:
    AnalysisContext context;

    DataFlowAnalysis(const AnalysisContext& context, const Symbol& symbol, const Statement& stmt) :
        AbstractFlowAnalysis(symbol, stmt), context(context) {}

    void joinState(DataFlowState& state, const DataFlowState& other) const {}
    void meetState(DataFlowState& state, const DataFlowState& other) const {}
    DataFlowState copyState(const DataFlowState& state) const { return {}; }
    DataFlowState unreachableState() const { return {}; }
    DataFlowState topState() const { return {}; }
};

} // namespace slang::analysis
