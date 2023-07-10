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
inline constexpr DiagCode EnforcePortSuffix(DiagSubsystem::Tidy, 2);
inline constexpr DiagCode NoLatchesOnDesign(DiagSubsystem::Tidy, 3);
inline constexpr DiagCode NoOldAlwaysSyntax(DiagSubsystem::Tidy, 4);
inline constexpr DiagCode AlwaysCombNonBlocking(DiagSubsystem::Tidy, 5);
inline constexpr DiagCode AlwaysFFBlocking(DiagSubsystem::Tidy, 6);
inline constexpr DiagCode EnforceModuleInstantiationPrefix(DiagSubsystem::Tidy, 7);
inline constexpr DiagCode OnlyANSIPortDecl(DiagSubsystem::Tidy, 8);

} // namespace slang::diag
