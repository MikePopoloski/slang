//------------------------------------------------------------------------------
//! @file TidyConfigPrinter.h
//! @brief Configuration file printing
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "TidyConfigParser.h"
#include "TidyFactory.h"
#include <fmt/format.h>

struct TidyConfigPrinter {

    static std::string toLower(const std::string_view input) {
        std::string result(input);
        std::transform(result.begin(), result.end(), result.begin(),
                       [](unsigned char c) { return std::tolower(c); });
        return result;
    }

    static std::string dumpConfig(TidyConfig const& tidyConfig) {
        std::string result = "Checks:\n";
        const auto& enabledChecks = Registry::getEnabledChecks();
        for (auto it = enabledChecks.begin(); it != enabledChecks.end(); ++it) {
            const auto check = Registry::create(*it);
            result += fmt::format("  {}-{}", toLower(toString(check->getKind())),
                                  TidyConfigParser::unformatCheckName(check->name()));
            if (std::next(it) != enabledChecks.end()) {
                result += ",\n";
            }
            else {
                result += "\n";
            }
        }
        result += "\n";

        result += "CheckConfigs:\n";
        const auto& configValues = tidyConfig.serialise();
        std::vector<std::pair<std::string, std::string>> populatedValues;
        for (auto& [name, value] : configValues) {
            if (value.empty()) {
                // Skip empty entries;
                continue;
            }
            populatedValues.push_back({name, value});
        }
        for (auto it = populatedValues.begin(); it != populatedValues.end(); ++it) {
            result += fmt::format("  {}: \"{}\"", it->first, it->second);
            if (std::next(it) != populatedValues.end()) {
                result += ",\n";
            }
            else {
                result += "\n";
            }
        }

        return result;
    }
};
