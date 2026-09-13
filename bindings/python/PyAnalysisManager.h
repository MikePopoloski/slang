//------------------------------------------------------------------------------
//! @file PyAnalysisManager.h
//! @brief Python representation of an analysis manager
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <nanobind/nanobind.h>
#include <vector>

#include "slang/analysis/AnalysisManager.h"
#include "slang/analysis/AnalysisOptions.h"

/// The Python representation of an analysis manager: the manager itself,
/// alongside the listener callables registered against it. The callables are
/// held here rather than on the manager so that the cyclic garbage collector
/// can reach them.
///
/// This is the type bound as `pyslang.analysis.AnalysisManager`, and it is
/// declared here so that other extension modules built on slang can accept an
/// analysis manager as an argument and reach it through `manager`.
struct PyAnalysisManager {
    slang::analysis::AnalysisManager manager;
    std::vector<nanobind::object> listeners;

    explicit PyAnalysisManager(slang::analysis::AnalysisOptions options) :
        manager(std::move(options)) {}
};
