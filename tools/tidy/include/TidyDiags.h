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
inline constexpr DiagCode XilinxDoNotCareValues(DiagSubsystem::Tidy, 9);
inline constexpr DiagCode CastSignedIndex(DiagSubsystem::Tidy, 10);
inline constexpr DiagCode NoDotStarInPortConnection(DiagSubsystem::Tidy, 11);
inline constexpr DiagCode NoImplicitPortNameInPortConnection(DiagSubsystem::Tidy, 12);
inline constexpr DiagCode AlwaysCombBlockNamed(DiagSubsystem::Tidy, 13);
inline constexpr DiagCode GenerateNamed(DiagSubsystem::Tidy, 14);
inline constexpr DiagCode NoDotVarInPortConnection(DiagSubsystem::Tidy, 15);
inline constexpr DiagCode NoLegacyGenerate(DiagSubsystem::Tidy, 16);
inline constexpr DiagCode AlwaysFFAssignmentOutsideConditional(DiagSubsystem::Tidy, 17);
inline constexpr DiagCode UnusedSensitiveSignal(DiagSubsystem::Tidy, 18);

} // namespace slang::diag
