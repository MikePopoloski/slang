//------------------------------------------------------------------------------
//! @file Debug.h
//! @brief Provide debug printing macros.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "Config.h"
#include <cstring>
#include <fmt/core.h>
#include <source_location>

namespace netlist {

inline const char* file_name(const char* file) {
    return strrchr(file, '/') ? strrchr(file, '/') + 1 : file;
}

template<typename... T>
void DebugMessage(const std::source_location& location, fmt::format_string<T...> fmt, T&&... args) {
    fmt::print("{}:{}: ", file_name(location.file_name()), location.line());
    fmt::print(fmt, std::forward<T>(args)...);
}

template<typename... T>
void InfoMessage(fmt::format_string<T...> fmt, T&&... args) {
    fmt::print(fmt, std::forward<T>(args)...);
}

} // namespace netlist

#ifdef DEBUG
#    define DEBUG_PRINT(str, ...)                                                          \
        if (netlist::Config::getInstance().debugEnabled) {                                 \
            DebugMessage(std::source_location::current(), str __VA_OPT__(, ) __VA_ARGS__); \
        }
#else
#    define DEBUG_PRINT(str, ...)
#endif

#define INFO_PRINT(str, ...)                         \
    if (!Config::getInstance().quietEnabled) {       \
        InfoMessage(str __VA_OPT__(, ) __VA_ARGS__); \
    }
