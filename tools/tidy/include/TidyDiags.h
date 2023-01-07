//------------------------------------------------------------------------------
//! @file TidyDiags.h
//! @brief Generated diagnostic enums for the Tidy subsystem
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/Diagnostics.h"

namespace slang::diag {

inline constexpr DiagCode OnlyAssignedOnReset(DiagSubsystem::Tidy, 0);
inline constexpr DiagCode RegisterNotAssignedOnReset(DiagSubsystem::Tidy, 1);

} // namespace slang::diag
