//------------------------------------------------------------------------------
//! @file TidyKind.h
//! @brief Enum describing the different kinds of checks
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <algorithm>
#include <array>
#include <optional>
#include <string>

#include "slang/util/Util.h"

namespace slang {
// clang-format off
#define KIND(x)   \
    x(Synthesis)  \
    x(Style)      \
    x(Assertion)  \
    x(Constraint) \
    x(UVM)
SLANG_ENUM(TidyKind, KIND)
#undef KIND
// clang-format on

inline std::optional<slang::TidyKind> tidyKindFromStr(std::string str) {
    std::transform(str.begin(), str.end(), str.begin(), ::tolower);
    if (str == "synthesis" || str == "synth")
        return slang::TidyKind::Synthesis;
    if (str == "style")
        return slang::TidyKind::Style;
    if (str == "assertion")
        return slang::TidyKind::Assertion;
    if (str == "constraint")
        return slang::TidyKind::Constraint;
    if (str == "uvm")
        return slang::TidyKind::UVM;
    return {};
}

} // namespace slang
