//------------------------------------------------------------------------------
//! @file AnalysisOptions.h
//! @brief Various options that control analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/Enum.h"

namespace slang::analysis {

/// Defines flags that control analysis behavior.
enum class SLANG_EXPORT AnalysisFlags {
    /// No flags specified.
    None = 0,

    /// Analysis should check for and report on unused symbols.
    CheckUnused = 1 << 0,

    /// 'unique' and 'priority' keywords are used to assume full case coverage.
    FullCaseUniquePriority = 1 << 1,

    /// Require X and Z bits be covered for full case coverage.
    /// If not set, only 0 and 1 bits are required.
    FullCaseFourState = 1 << 2,

    /// Allow multi-driven subroutine local variables.
    AllowMultiDrivenLocals = 1 << 3,

    /// Signals driven by an always_comb are normally not allowed to be driven
    /// by any other process. This flag allows initial blocks to
    /// also drive such signals.
    AllowDupInitialDrivers = 1 << 4,
};
SLANG_BITMASK(AnalysisFlags, AllowDupInitialDrivers)

/// Contains various options that can control analysis behavior.
struct SLANG_EXPORT AnalysisOptions {
    /// Flags that control analysis behavior.
    bitmask<AnalysisFlags> flags;

    /// The number of threads to use for analysis.
    uint32_t numThreads = 0;

    /// The maximum number of case analysis steps to perform before giving up.
    uint32_t maxCaseAnalysisSteps = 65535;

    /// The maximum number of loop analysis steps to perform before giving up.
    uint32_t maxLoopAnalysisSteps = 65535;
};

} // namespace slang::analysis
