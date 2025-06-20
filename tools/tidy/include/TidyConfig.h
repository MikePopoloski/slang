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
#include <fmt/ranges.h>
#include <regex>
#include <slang/util/TypeTraits.h>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "slang/diagnostics/Diagnostics.h"

class TidyConfig {
    friend class TidyConfigParser;

public:
    /// Configuration values across all checks.
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
        std::vector<std::string> inputPortPrefix;
        std::vector<std::string> outputPortPrefix;
        std::vector<std::string> inoutPortPrefix;
    };

    /// Default TidyConfig constructor which will set the default check's configuration values
    TidyConfig();

    /// Returns whether a check is enabled or not
    [[nodiscard]] bool isCheckEnabled(slang::TidyKind kind, const std::string& checkName) const;

    /// Returns the user-specified severity of the check
    [[nodiscard]] auto getCheckSeverity(slang::TidyKind kind, const std::string& checkName) const
        -> std::optional<slang::DiagnosticSeverity>;

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

    /// Serialise the tidy config for printing in the config file format.
    std::vector<std::pair<std::string, std::string>> serialise() const {
        const auto& cfg = getCheckConfigs();
        auto joinVec = [](const auto& vec) { return fmt::format("{}", fmt::join(vec, "|")); };
        return {
            {"clkName", cfg.clkName},
            {"resetName", cfg.resetName},
            {"clkNameRegexString", cfg.clkNameRegexString},
            {"resetIsActiveHigh", cfg.resetIsActiveHigh ? "true" : "false"},
            {"inputPortSuffix", joinVec(cfg.inputPortSuffix)},
            {"outputPortSuffix", joinVec(cfg.outputPortSuffix)},
            {"inoutPortSuffix", joinVec(cfg.inoutPortSuffix)},
            {"moduleInstantiationPrefix", cfg.moduleInstantiationPrefix},
            {"inputPortPrefix", joinVec(cfg.inputPortPrefix)},
            {"outputPortPrefix", joinVec(cfg.outputPortPrefix)},
            {"inoutPortPrefix", joinVec(cfg.inoutPortPrefix)},
        };
    }

private:
    /// Possible status of the checks.
    enum class CheckStatus { ENABLED, DISABLED };

    /// Configuration for each check.
    struct CheckOptions {

        // Whether the check is enabled or disabled.
        CheckStatus status{CheckStatus::ENABLED};

        // Whether there is a user-specified severity.
        std::optional<slang::DiagnosticSeverity> severity;
    };

    CheckConfigs checkConfigs;

    std::unordered_map<slang::TidyKind, std::unordered_map<std::string, CheckOptions>> checkKinds;

    // List of files that won't be checked by slang-tidy
    std::vector<std::string> skipFiles;

    // List of paths that won't be checked by slang-tidy
    std::vector<std::string> skipPaths;

    /// Enables or disables all the implemented checks based on status
    void toggleAl(CheckStatus status);

    /// Enables or disables all the checks implemented in the TidyKind provided based on status
    void toggleGroup(slang::TidyKind kind, CheckStatus status,
                     std::optional<slang::DiagnosticSeverity> severity);

    /// Disables or enables a particular check implemented in the TidyKind provided based on status.
    /// It will return false if the check do not exist.
    [[nodiscard]] bool toggleCheck(slang::TidyKind kind, const std::string& checkName,
                                   CheckStatus status,
                                   std::optional<slang::DiagnosticSeverity> severity);

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
        else if (configName == "inputPortPrefix") {
            visit(checkConfigs.inputPortPrefix);
            return;
        }
        else if (configName == "outputPortPrefix") {
            visit(checkConfigs.outputPortPrefix);
            return;
        }
        else if (configName == "inoutPortPrefix") {
            visit(checkConfigs.inoutPortPrefix);
            return;
        }
        SLANG_THROW(std::invalid_argument(fmt::format("The check: {} does not exist", configName)));
    }
};
