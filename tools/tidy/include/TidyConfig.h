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
#include <regex>
#include <slang/util/TypeTraits.h>
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
        std::string clkNameRegexString;
        std::regex clkNameRegexPattern;
        std::string resetName;
        bool resetIsActiveHigh;
        std::vector<std::string> inputPortSuffix;
        std::vector<std::string> outputPortSuffix;
        std::vector<std::string> inoutPortSuffix;
        std::string moduleInstantiationPrefix;
    };

    /// Default TidyConfig constructor which will set the default check's configuration values
    TidyConfig();

    /// Returns whether a check is enabled or not
    [[nodiscard]] bool isCheckEnabled(slang::TidyKind kind, const std::string& checkName) const;

    /// Returns the check config object
    inline const CheckConfigs& getCheckConfigs() const { return checkConfigs; }

    /// Returns the check config object
    inline CheckConfigs& getCheckConfigs() { return checkConfigs; }

    // Returns a vector containing the file names that won't be checked by slang-tidy
    inline const std::vector<std::string>& getSkipFiles() const { return skipFiles; }

    // Returns a vector containing the paths names that won't be checked by slang-tidy
    inline const std::vector<std::string>& getSkipPaths() const { return skipPaths; }

    // Adds a new file into the list of skipped files
    void addSkipFile(const std::string& path);
    void addSkipFile(const std::vector<std::string>& paths);

    // Adds a new path into the list of skipped paths
    void addSkipPath(const std::string& path);
    void addSkipPath(const std::vector<std::string>& paths);

private:
    CheckConfigs checkConfigs;

    /// Possible status of the checks
    enum class CheckStatus { ENABLED, DISABLED };

    std::unordered_map<slang::TidyKind, std::unordered_map<std::string, CheckStatus>> checkKinds;

    // List of files that won't be checked by slang-tidy
    std::vector<std::string> skipFiles;

    // List of paths that won't be checked by slang-tidy
    std::vector<std::string> skipPaths;

    /// Enables or disables all the implemented checks based on status
    void toggleAl(CheckStatus status);

    /// Enables or disables all the checks implemented in the TidyKind provided based on status
    void toggleGroup(slang::TidyKind kind, CheckStatus status);

    /// Disables or enables a particular check implemented in the TidyKind provided based on status.
    /// It will return false if the check do not exist.
    [[nodiscard]] bool toggleCheck(slang::TidyKind kind, const std::string& checkName,
                                   CheckStatus status);

    /// Visits the value of a check config. Will throw an invalid_argument exception
    /// if the configName is unknown
    template<typename Visitor>
    void visitConfig(std::string const& configName, Visitor visit) {
        if (configName == "clkName") {
            visit(checkConfigs.clkName);
            return;
        }
        else if (configName == "resetName") {
            visit(checkConfigs.resetName);
            return;
        }
        else if (configName == "clkNameRegexString") {
            visit(checkConfigs.clkNameRegexString);
            checkConfigs.clkNameRegexPattern = std::regex(checkConfigs.clkNameRegexString);
            return;
        }
        else if (configName == "resetIsActiveHigh") {
            visit(checkConfigs.resetIsActiveHigh);
            return;
        }
        else if (configName == "inputPortSuffix") {
            visit(checkConfigs.inputPortSuffix);
            return;
        }
        else if (configName == "outputPortSuffix") {
            visit(checkConfigs.outputPortSuffix);
            return;
        }
        else if (configName == "inoutPortSuffix") {
            visit(checkConfigs.inoutPortSuffix);
            return;
        }
        else if (configName == "moduleInstantiationPrefix") {
            visit(checkConfigs.moduleInstantiationPrefix);
            return;
        }
        SLANG_THROW(std::invalid_argument(fmt::format("The check: {} does not exist", configName)));
    }
};
