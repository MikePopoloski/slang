//------------------------------------------------------------------------------
//! @file NetlistVisitorOptions.h
//! @brief Options controlling the way the netlist is created.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <optional>

/// Hold various options controlling the way the netlist is created.
struct NetlistVisitorOptions {

    /// If enabled, unroll for loops in procedural blocks.
    bool unrollForLoops{false};
};
