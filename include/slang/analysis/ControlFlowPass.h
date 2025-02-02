//------------------------------------------------------------------------------
//! @file ControlFlowPass.h
//! @brief Control flow analysis pass
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/analysis/AbstractFlowAnalysis.h"

namespace slang::analysis {

struct ControlFlowState {};

class ControlFlowPass : public AbstractFlowAnalysis<ControlFlowPass, ControlFlowState> {
public:
    ControlFlowPass(const Symbol& symbol, const Statement& stmt) :
        AbstractFlowAnalysis(symbol, stmt) {}

    void joinState(ControlFlowState& state, const ControlFlowState& other) const {}
    void meetState(ControlFlowState& state, const ControlFlowState& other) const {}
    ControlFlowState unreachableState() const { return {}; }
    ControlFlowState topState() const { return {}; }
};

} // namespace slang::analysis
