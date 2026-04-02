//------------------------------------------------------------------------------
// MemStatsUtil.h
// Shared utilities for CST and AST memory statistics.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <cstddef>
#include <cstdio>
#include <fmt/format.h>
#include <fstream>
#include <string>

namespace slang {

static inline std::string memStatsFmtBytes(size_t bytes) {
    auto d = static_cast<double>(bytes);
    if (bytes < 1024)
        return fmt::format("{} B", bytes);
    else if (bytes < 1024 * 1024)
        return fmt::format("{:.2f} KB", d / 1024.0);
    else if (bytes < 1024 * 1024 * 1024)
        return fmt::format("{:.2f} MB", d / (1024.0 * 1024.0));
    else
        return fmt::format("{:.2f} GB", d / (1024.0 * 1024.0 * 1024.0));
}

// Returns the current RSS (resident set size) of the process in bytes.
// Reads /proc/self/status on Linux; returns 0 on unsupported platforms.
static inline size_t memStatsGetProcessRSS() {
#if defined(__linux__)
    std::ifstream status("/proc/self/status");
    std::string line;
    while (std::getline(status, line)) {
        if (line.rfind("VmRSS:", 0) == 0) {
            size_t kib = 0;
            if (std::sscanf(line.c_str() + 6, "%zu", &kib) == 1)
                return kib * 1024;
        }
    }
#endif
    return 0;
}

} // namespace slang
