//------------------------------------------------------------------------------
//! @file TidyKind.h
//! @brief Enum describing the different kinds of checks
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <algorithm>
#include <optional>
#include <string>

#include "slang/util/Util.h"

namespace slang {
// clang-format off
#define KIND(x)  \
    x(Synthesis) \
    x(Ports)
SLANG_ENUM(TidyKind, KIND)
#undef KIND
// clang-format on

inline std::optional<slang::TidyKind> tidy_kind_from_str(std::string str) {
    std::transform(str.begin(), str.end(), str.begin(), ::tolower);
    if (str == "synthesis")
        return slang::TidyKind::Synthesis;
    if (str == "ports")
        return slang::TidyKind::Ports;
    return {};
}

} // namespace slang
