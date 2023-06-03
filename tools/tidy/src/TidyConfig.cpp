//------------------------------------------------------------------------------
//! @file TidyConfig.cpp
//! @brief Configuration of the tidy tool
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "TidyConfig.h"

#include "TidyFactory.h"

using slang::TidyKind;

TidyConfig::TidyConfig() {
    checkConfigs.clkName = "clk_i";
    checkConfigs.resetName = "rst_ni";
    checkConfigs.resetIsActiveHigh = true;
    checkConfigs.inputPortSuffix = "_i";
    checkConfigs.outputPortSuffix = "_o";
    checkConfigs.inoutPortSuffix = "_io";

    auto portsChecks = std::unordered_map<std::string, CheckStatus>();
    portsChecks.emplace("EnforcePortSuffix", CheckStatus::ENABLED);
    portsChecks.emplace("NoOldAlwaysCombSyntax", CheckStatus::ENABLED);
    checkKinds.insert({slang::TidyKind::Style, portsChecks});

    auto synthesisChecks = std::unordered_map<std::string, CheckStatus>();
    synthesisChecks.emplace("OnlyAssignedOnReset", CheckStatus::ENABLED);
    synthesisChecks.emplace("RegisterHasNoReset", CheckStatus::ENABLED);
    synthesisChecks.emplace("NoLatchesOnDesign", CheckStatus::ENABLED);
    checkKinds.insert({slang::TidyKind::Synthesis, synthesisChecks});
}

void TidyConfig::toggle_all(CheckStatus status) {
    for (auto &checkKind: checkKinds) {
        for (auto &check: checkKind.second)
            check.second = status;
    }
}

void TidyConfig::toggle_group(slang::TidyKind kind, CheckStatus status) {
    for (auto& check : checkKinds.at(kind))
        check.second = status;
}

bool TidyConfig::toggle_check(slang::TidyKind kind, const std::string &checkName, CheckStatus status) {
    auto registeredChecks = Registry::get_registered_checks();
    if (std::find(registeredChecks.begin(), registeredChecks.end(), checkName) ==
        registeredChecks.end()) {
        return false;
    }
    checkKinds.at(kind).at(checkName) = status;
    return true;
}

bool TidyConfig::is_check_enabled(slang::TidyKind kind, const std::string &checkName) const {
    return checkKinds.at(kind).at(checkName) == CheckStatus::ENABLED;
}
