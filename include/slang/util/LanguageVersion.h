//------------------------------------------------------------------------------
//! @file LanguageVersion.h
//! @brief Enum specify SystemVerilog language versions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <string_view>

namespace slang {

/// Specifies SystemVerilog language versions and Standard Delay Format (SDF) standard.
enum class LanguageVersion { v1800_2017, v1800_2023, v1497_2001, Default = v1800_2017 };

inline std::string_view toString(LanguageVersion lv) {
    switch (lv) {
        case LanguageVersion::v1800_2017:
            return "1800-2017";
        case LanguageVersion::v1800_2023:
            return "1800-2023";
        case LanguageVersion::v1497_2001:
            return "1497-2001";
        default:
            return "";
    }
}

} // namespace slang
