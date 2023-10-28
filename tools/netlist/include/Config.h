//------------------------------------------------------------------------------
//! @file Config.h
//! @brief Provide singleton configuration class debug printing macro.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

namespace netlist {

/// A singleton to hold global configuration options.
class Config {
public:
    bool debugEnabled{false};
    bool quietEnabled{false};

    Config() = default;

    static Config& getInstance() {
        static Config instance;
        return instance;
    }

    // Prevent copies from being made.
    Config(Config const&) = delete;
    void operator=(Config const&) = delete;
};

} // namespace netlist
