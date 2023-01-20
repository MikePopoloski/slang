//------------------------------------------------------------------------------
//! @file tidy.h
//! @brief The slang linter
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "fmt/color.h"
#include "fmt/format.h"
#include "include/TidyFactory.h"
#include <unordered_set>

#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/Driver.h"
#include "slang/util/Version.h"

using namespace slang;

int main(int argc, char** argv) {

    driver::Driver driver;
    driver.addStandardArgs();

    std::optional<bool> showHelp;
    std::optional<bool> showVersion;
    std::optional<bool> quiet;
    driver.cmdLine.add("-h,--help", showHelp, "Display available options");
    driver.cmdLine.add("--version", showVersion, "Display version information and exit");
    driver.cmdLine.add("-q,--quiet", quiet, "Suppress non-essential output");

    std::optional<bool> printDescriptions;
    std::optional<bool> printShortDescriptions;
    driver.cmdLine.add("--print-descriptions", printDescriptions,
                       "Displays the description of each check and exits");
    driver.cmdLine.add("--print-short-descriptions", printShortDescriptions,
                       "Displays the short description of each check and exits");

    std::optional<bool> disableSynthesisChecks;
    std::vector<std::string> disabledCheckNames;
    driver.cmdLine.add("--disable-synthesis-checks", disableSynthesisChecks,
                       "Disables the synthesis checks");
    driver.cmdLine.add("--disable-checks", disabledCheckNames,
                       "Names of checks that will be disabled");

    std::optional<bool> onlySynthesisChecks;
    driver.cmdLine.add("--only-synthesis-checks", onlySynthesisChecks,
                       "Disables the synthesis checks");

    std::optional<std::string> clockName;
    std::optional<std::string> resetName;
    std::optional<bool> resetActiveHigh;
    driver.cmdLine.add("--clock-name", clockName, "Name of the design clock signal");
    driver.cmdLine.add("--reset-name", resetName, "Name of the design reset signal");
    driver.cmdLine.add("--reset-active-high", resetActiveHigh,
                       "Indicates that the reset is active high. By default reset is active low");

    if (!driver.parseCommandLine(argc, argv))
        return 1;

    if (showHelp) {
        slang::OS::print(
            fmt::format("{}", driver.cmdLine.getHelpText("slang SystemVerilog linter")));
        return 0;
    }

    if (showVersion) {
        OS::print(fmt::format("slang-tidy version {}.{}.{}+{}\n", VersionInfo::getMajor(),
                              VersionInfo::getMinor(), VersionInfo::getPatch(),
                              VersionInfo::getHash()));
        return 0;
    }

    if (!disabledCheckNames.empty()) {
        auto allRegisteredChecks = Registry::get_registered();
        for (const auto& name : disabledCheckNames) {
            if (!std::count(allRegisteredChecks.begin(), allRegisteredChecks.end(), name)) {
                slang::OS::printE(
                    fmt::format("the check {} provided in --disable-check do not exist\n", name));
                return 6;
            }
        }
    }

    std::unordered_set<slang::TidyKind> disabledCheckKinds;
    if (disableSynthesisChecks)
        disabledCheckKinds.insert(TidyKind::Synthesis);

    auto filter_func = [&](const Registry::RegistryItem& item) {
        if (std::count(disabledCheckNames.begin(), disabledCheckNames.end(), item.first))
            return false;
        if (disabledCheckKinds.count(item.second.kind))
            return false;
        if (onlySynthesisChecks)
            return item.second.kind == slang::TidyKind::Synthesis;
        return true;
    };

    if (printDescriptions || printShortDescriptions) {
        bool first = true;
        for (const auto& check_name : Registry::get_registered(filter_func)) {
            const auto check = Registry::create(check_name);
            if (first)
                first = false;
            else
                OS::print("\n");
            OS::print(fmt::format(fmt::emphasis::bold, "[{}]\n", check->name()));
            if (printDescriptions)
                OS::print(fmt::format("{}", check->description()));
            else
                OS::print(fmt::format("{}\n", check->shortDescription()));
        }
        return 0;
    }

    if (!driver.processOptions())
        return 2;

    std::unique_ptr<ast::Compilation> compilation;
    bool compilation_ok;
    try {
        compilation_ok = driver.parseAllSources();
        compilation = driver.createCompilation();
        compilation_ok &= driver.reportCompilation(*compilation, true);
    }
    catch (const std::exception& e) {
        slang::OS::printE(fmt::format("internal compiler error: {}\n", e.what()));
        return 4;
    }

    if (!compilation_ok) {
        slang::OS::print("slang-tidy: errors found during compilation\n");
        return 1;
    }

    DiagnosticEngine diagEngine(*compilation->getSourceManager());
    auto textDiagClient = std::make_shared<TextDiagnosticClient>();
    textDiagClient->showColors(true);
    diagEngine.addClient(textDiagClient);

    int ret_code = 0;

    Registry::initialize_default_check_config();
    if (clockName)
        Registry::set_check_config_clock_name(clockName.value());
    if (resetName)
        Registry::set_check_config_reset_name(resetName.value());
    if (resetActiveHigh)
        Registry::set_check_config_reset_active_high(true);

    for (const auto& check_name : Registry::get_registered(filter_func)) {
        const auto check = Registry::create(check_name);
        OS::print(fmt::format("[{}]", check->name()));

        diagEngine.setMessage(check->diagCode(), check->diagString());
        diagEngine.setSeverity(check->diagCode(), check->diagSeverity());

        auto checkOk = check->check(compilation->getRoot());
        if (!checkOk) {
            ret_code = 5;
            OS::print(fmt::emphasis::bold | fmt::fg(fmt::color::red), " FAIL\n");
            const auto& diags = check->getDiagnostics();
            for (const auto& diag : diags)
                diagEngine.issue(diag);
            OS::print(fmt::format("{}\n", textDiagClient->getString()));
            textDiagClient->clear();
        }
        else {
            OS::print(fmt::emphasis::bold | fmt::fg(fmt::color::green), " PASS\n");
        }
    }

    return ret_code;
}
