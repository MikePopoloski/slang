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
#include <vector>

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
    [[nodiscard]] bool isCheckEnabled(slang::TidyKind kind, const std::string& checkName) const;

    /// Returns the check config object
    inline const CheckConfigs& getCheckConfigs() const { return checkConfigs; }

    // Returns a vector containing the file names that won't be checked by slang-tidy
    inline const std::vector<std::string>& getSkipFiles() const { return skipFiles; }

    // Adds a new file into the list of skipped files
    void addSkipFile(const std::string& path);
    void addSkipFile(std::vector<std::string> paths);

private:
    CheckConfigs checkConfigs;

    /// Possible status of the checks
    enum class CheckStatus { ENABLED, DISABLED };

    std::unordered_map<slang::TidyKind, std::unordered_map<std::string, CheckStatus>> checkKinds;

    // List of files that won't be checked by slang-tidy
    std::vector<std::string> skipFiles;

    /// Enables or disables all the implemented checks based on status
    void toggleAl(CheckStatus status);

    /// Enables or disables all the checks implemented in the TidyKind provided based on status
    void toggleGroup(slang::TidyKind kind, CheckStatus status);

    /// Disables or enables a particular check implemented in the TidyKind provided based on status.
    /// It will return false if the check do not exist.
    [[nodiscard]] bool toggleCheck(slang::TidyKind kind, const std::string& checkName,
                                   CheckStatus status);

    /// Sets the value of a check config. Will throw an invalid_argument exception if the type of
    /// value doesn't match the config type
    template<typename T>
    void setConfig(const std::string& configName, T value) {
        if (configName == "clkName") {
            innerSetConfig(checkConfigs.clkName, value);
            return;
        }
        else if (configName == "resetName") {
            innerSetConfig(checkConfigs.resetName, value);
            return;
        }
        else if (configName == "resetIsActiveHigh") {
            innerSetConfig(checkConfigs.resetIsActiveHigh, value);
            return;
        }
        else if (configName == "inputPortSuffix") {
            innerSetConfig(checkConfigs.inputPortSuffix, value);
            return;
        }
        else if (configName == "outputPortSuffix") {
            innerSetConfig(checkConfigs.outputPortSuffix, value);
            return;
        }
        else if (configName == "inoutPortSuffix") {
            innerSetConfig(checkConfigs.inoutPortSuffix, value);
            return;
        }

        SLANG_THROW(std::invalid_argument(fmt::format("The check: {} does not exist", configName)));
    }

    template<typename T, typename U>
    void innerSetConfig(T& config, U value) {
        if constexpr (std::is_same_v<T, U>)
            config = value;
        else
            SLANG_THROW(
                std::invalid_argument(fmt::format("check config expected a {} found {}",
                                                  slang::typeName<T>(), slang::typeName<U>())));
    }
};
