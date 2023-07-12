// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyConfig.h"

#include "TidyFactory.h"
#include <filesystem>
#include <utility>

TidyConfig::TidyConfig() {
    checkConfigs.clkName = "clk_i";
    checkConfigs.resetName = "rst_ni";
    checkConfigs.resetIsActiveHigh = true;
    checkConfigs.inputPortSuffix = {"_i"};
    checkConfigs.outputPortSuffix = {"_o"};
    checkConfigs.inoutPortSuffix = {"_io"};
    checkConfigs.moduleInstantiationPrefix = "i_";

    auto styleChecks = std::unordered_map<std::string, CheckStatus>();
    styleChecks.emplace("AlwaysCombNonBlocking", CheckStatus::ENABLED);
    styleChecks.emplace("AlwaysFFBlocking", CheckStatus::ENABLED);
    styleChecks.emplace("EnforcePortSuffix", CheckStatus::ENABLED);
    styleChecks.emplace("NoOldAlwaysSyntax", CheckStatus::ENABLED);
    styleChecks.emplace("EnforceModuleInstantiationPrefix", CheckStatus::ENABLED);
    styleChecks.emplace("OnlyANSIPortDecl", CheckStatus::ENABLED);
    checkKinds.insert({slang::TidyKind::Style, styleChecks});

    auto synthesisChecks = std::unordered_map<std::string, CheckStatus>();
    synthesisChecks.emplace("NoLatchesOnDesign", CheckStatus::ENABLED);
    synthesisChecks.emplace("OnlyAssignedOnReset", CheckStatus::ENABLED);
    synthesisChecks.emplace("RegisterHasNoReset", CheckStatus::ENABLED);
    checkKinds.insert({slang::TidyKind::Synthesis, synthesisChecks});
}

void TidyConfig::addSkipFile(const std::string& path) {
    skipFiles.push_back(std::filesystem::path(path).filename().string());
}

void TidyConfig::addSkipFile(std::vector<std::string> paths) {
    skipFiles = std::move(paths);
}

void TidyConfig::toggleAl(CheckStatus status) {
    for (auto& checkKind : checkKinds) {
        for (auto& check : checkKind.second)
            check.second = status;
    }
}

void TidyConfig::toggleGroup(slang::TidyKind kind, CheckStatus status) {
    for (auto& check : checkKinds.at(kind))
        check.second = status;
}

bool TidyConfig::toggleCheck(slang::TidyKind kind, const std::string& checkName,
                             CheckStatus status) {
    auto registeredChecks = Registry::getRegisteredChecks();
    if (std::find(registeredChecks.begin(), registeredChecks.end(), checkName) ==
        registeredChecks.end()) {
        return false;
    }
    checkKinds.at(kind).at(checkName) = status;
    return true;
}

bool TidyConfig::isCheckEnabled(slang::TidyKind kind, const std::string& checkName) const {
    return checkKinds.at(kind).at(checkName) == CheckStatus::ENABLED;
}
