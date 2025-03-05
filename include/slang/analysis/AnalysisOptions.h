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
    FullCaseUniquePriority = 1 << 1
};
SLANG_BITMASK(AnalysisFlags, FullCaseUniquePriority)

/// Contains various options that can control analysis behavior.
struct SLANG_EXPORT AnalysisOptions {
    /// Flags that control analysis behavior.
    bitmask<AnalysisFlags> flags;

    /// The number of threads to use for analysis.
    uint32_t numThreads = 0;
};

} // namespace slang::analysis
