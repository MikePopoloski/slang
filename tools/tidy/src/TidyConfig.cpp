// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include "TidyConfig.h"

#include "TidyFactory.h"
#include <filesystem>

namespace fs = std::filesystem;

TidyConfig::TidyConfig() {
    checkConfigs.clkName = "clk_i";
    checkConfigs.clkNameRegexString = "clk\\S*|clock\\S*";
    checkConfigs.clkNameRegexPattern = std::regex(checkConfigs.clkNameRegexString);
    checkConfigs.resetName = "rst_ni";
    checkConfigs.resetIsActiveHigh = true;
    checkConfigs.inputPortSuffix = {"_i"};
    checkConfigs.outputPortSuffix = {"_o"};
    checkConfigs.inoutPortSuffix = {"_io"};
    checkConfigs.moduleInstantiationPrefix = "i_";
    checkConfigs.inputPortPrefix = {""};
    checkConfigs.outputPortPrefix = {""};
    checkConfigs.inoutPortPrefix = {""};

    auto styleChecks = std::unordered_map<std::string, CheckOptions>();
    styleChecks.emplace("AlwaysCombNonBlocking", CheckOptions());
    styleChecks.emplace("AlwaysFFBlocking", CheckOptions());
    styleChecks.emplace("EnforcePortPrefix", CheckOptions());
    styleChecks.emplace("EnforcePortSuffix", CheckOptions());
    styleChecks.emplace("NoOldAlwaysSyntax", CheckOptions());
    styleChecks.emplace("EnforceModuleInstantiationPrefix", CheckOptions());
    styleChecks.emplace("OnlyANSIPortDecl", CheckOptions());
    styleChecks.emplace("NoDotStarInPortConnection", CheckOptions());
    styleChecks.emplace("NoImplicitPortNameInPortConnection", CheckOptions());
    styleChecks.emplace("AlwaysCombBlockNamed", CheckOptions());
    styleChecks.emplace("GenerateNamed", CheckOptions());
    styleChecks.emplace("NoDotVarInPortConnection", CheckOptions());
    styleChecks.emplace("NoLegacyGenerate", CheckOptions());
    checkKinds.insert({slang::TidyKind::Style, styleChecks});

    auto synthesisChecks = std::unordered_map<std::string, CheckOptions>();
    synthesisChecks.emplace("NoLatchesOnDesign", CheckOptions());
    synthesisChecks.emplace("OnlyAssignedOnReset", CheckOptions());
    synthesisChecks.emplace("RegisterHasNoReset", CheckOptions());
    synthesisChecks.emplace("XilinxDoNotCareValues", CheckOptions());
    synthesisChecks.emplace("CastSignedIndex", CheckOptions());
    synthesisChecks.emplace("AlwaysFFAssignmentOutsideConditional", CheckOptions());
    synthesisChecks.emplace("UnusedSensitiveSignal", CheckOptions());
    synthesisChecks.emplace("UndrivenRange", CheckOptions());
    checkKinds.insert({slang::TidyKind::Synthesis, synthesisChecks});
}

void TidyConfig::addSkipFile(const std::string& path) {
    skipFiles.push_back(fs::path(path).filename().string());
}

void TidyConfig::addSkipFile(const std::vector<std::string>& paths) {
    for (const auto& path : paths)
        skipFiles.push_back(fs::path(path).filename().string());
}

void TidyConfig::addSkipPath(const std::string& path) {
    skipPaths.push_back(fs::path(path).parent_path().string());
}

void TidyConfig::addSkipPath(const std::vector<std::string>& paths) {
    for (const auto& path : paths)
        skipPaths.push_back(fs::path(path).parent_path().string());
}

void TidyConfig::toggleAl(CheckStatus status) {
    for (auto& checkKind : checkKinds) {
        for (auto& check : checkKind.second)
            check.second.status = status;
    }
}

void TidyConfig::toggleGroup(slang::TidyKind kind, CheckStatus status,
                             std::optional<slang::DiagnosticSeverity> severity) {
    for (auto& check : checkKinds.at(kind)) {
        check.second.status = status;
        check.second.severity = severity;
    }
}

bool TidyConfig::toggleCheck(slang::TidyKind kind, const std::string& checkName, CheckStatus status,
                             std::optional<slang::DiagnosticSeverity> severity) {
    auto registeredChecks = Registry::getRegisteredChecks();
    if (std::find(registeredChecks.begin(), registeredChecks.end(), checkName) ==
        registeredChecks.end()) {
        return false;
    }

    auto& checkNames = checkKinds.at(kind);
    // Check that checker name is presence at target group
    if (checkNames.count(checkName)) {
        checkNames.at(checkName).status = status;
        checkNames.at(checkName).severity = severity;
        return true;
    }

    return false;
}

bool TidyConfig::isCheckEnabled(slang::TidyKind kind, const std::string& checkName) const {
    return checkKinds.at(kind).at(checkName).status == CheckStatus::ENABLED;
}

auto TidyConfig::getCheckSeverity(slang::TidyKind kind, const std::string& checkName) const
    -> std::optional<slang::DiagnosticSeverity> {
    return checkKinds.at(kind).at(checkName).severity;
}
