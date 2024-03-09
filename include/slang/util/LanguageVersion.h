//------------------------------------------------------------------------------
//! @file LanguageVersion.h
//! @brief Enum specify SystemVerilog language versions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

namespace slang {

/// Specifies SystemVerilog language versions.
enum class LanguageVersion { v1800_2017, v1800_2023, Default = v1800_2017 };

} // namespace slang
