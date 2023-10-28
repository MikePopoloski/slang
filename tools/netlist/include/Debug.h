//------------------------------------------------------------------------------
//! @file Debug.h
//! @brief Provide debug printing macros.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "Config.h"
#include <fmt/core.h>

namespace netlist {

template<typename... T>
void DebugMessage(const char* filename, const int line, fmt::format_string<T...> fmt, T&&... args) {
    fmt::print("{}:{}: ", filename, line);
    fmt::print(fmt, std::forward<T>(args)...);
}

template<typename... T>
void InfoMessage(fmt::format_string<T...> fmt, T&&... args) {
    fmt::print(fmt, std::forward<T>(args)...);
}

} // namespace netlist

#ifdef DEBUG
#    define DEBUG_PRINT(str, ...)                                             \
        if (netlist::Config::getInstance().debugEnabled) {                    \
            DebugMessage(__FILE__, __LINE__, str __VA_OPT__(, ) __VA_ARGS__); \
        }
#else
#    define DEBUG_PRINT(str, ...)
#endif

#define INFO_PRINT(str, ...)                         \
    if (!Config::getInstance().quietEnabled) {       \
        InfoMessage(str __VA_OPT__(, ) __VA_ARGS__); \
    }
