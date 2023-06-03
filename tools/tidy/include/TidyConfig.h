//------------------------------------------------------------------------------
//! @file TidyConfig.h
//! @brief Configuration of the tidy tool
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "TidyKind.h"
#include <algorithm>
#include <fmt/format.h>
#include <slang/util/CppTypePrinter.h>
#include <string>
#include <unordered_map>
#include <unordered_set>

class TidyConfig {
    friend class TidyConfigParser;

public:
    /// Configuration values of checks
    struct CheckConfigs {
        std::string clkName;
        std::string resetName;
        bool resetIsActiveHigh;
        std::string inputPortSuffix;
        std::string outputPortSuffix;
        std::string inoutPortSuffix;
    };

    /// Default TidyConfig constructor which will set the default check's configuration values
    TidyConfig();

    /// Returns whether a check is enabled or not
    [[nodiscard]] bool is_check_enabled(slang::TidyKind kind, const std::string &checkName) const;

    /// Returns the check config object
    inline const CheckConfigs &get_check_configs() const { return checkConfigs; }

private:
    CheckConfigs checkConfigs;

    /// Possible status of the checks
    enum class CheckStatus {
        ENABLED, DISABLED
    };

    std::unordered_map<slang::TidyKind, std::unordered_map<std::string, CheckStatus>> checkKinds;

    /// Enables or disables all the implemented checks based on status
    void toggle_all(CheckStatus status);

    /// Enables or disables all the checks implemented in the TidyKind provided based on status
    void toggle_group(slang::TidyKind kind, CheckStatus status);

    /// Disables or enables a particular check implemented in the TidyKind provided based on status.
    /// It will return false if the check do not exist.
    [[nodiscard]] bool toggle_check(slang::TidyKind kind, const std::string &checkName, CheckStatus status);

    /// Sets the value of a check config. Will throw an invalid_argument exception if the type of
    /// value doesn't match the config type
    template<typename T>
    void set_config(const std::string &configName, T value) {
        if (configName == "clkName") {
            inner_set_config(checkConfigs.clkName, value);
            return;
        } else if (configName == "resetName") {
            inner_set_config(checkConfigs.resetName, value);
            return;
        } else if (configName == "resetIsActiveHigh") {
            inner_set_config(checkConfigs.resetIsActiveHigh, value);
            return;
        } else if (configName == "inputPortSuffix") {
            inner_set_config(checkConfigs.inputPortSuffix, value);
            return;
        } else if (configName == "outputPortSuffix") {
            inner_set_config(checkConfigs.outputPortSuffix, value);
            return;
        } else if (configName == "inoutPortSuffix") {
            inner_set_config(checkConfigs.inoutPortSuffix, value);
            return;
        }

        SLANG_THROW(std::invalid_argument(fmt::format("The check: {} does not exist", configName)));
    }

    template<typename T, typename U>
    void inner_set_config(T &config, U value) {
        if constexpr (std::is_same_v<T, U>)
            config = value;
        else
            SLANG_THROW(std::invalid_argument(
                    fmt::format("check config expected a {} found {}", slang::typeName<T>(), slang::typeName<U>())));
    }
};
