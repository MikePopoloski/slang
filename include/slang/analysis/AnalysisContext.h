//------------------------------------------------------------------------------
//! @file AnalysisContext.h
//! @brief Various bits of state needed to perform analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/util/IntervalMap.h"

namespace slang {

class BumpAllocator;
class Diagnostics;

} // namespace slang

namespace slang::analysis {

using AssignedBitsMap = IntervalMap<uint64_t, std::monostate, 3>;

/// Holds various bits of state needed to perform analysis.
class AnalysisContext {
public:
    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    AssignedBitsMap::allocator_type& assignedBitsAllocator;
};

} // namespace slang::analysis
