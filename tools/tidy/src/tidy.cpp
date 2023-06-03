//------------------------------------------------------------------------------
//! @file tidy.h
//! @brief The slang linter
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "TidyConfigParser.h"
#include "TidyFactory.h"
#include "fmt/color.h"
#include "fmt/format.h"
#include <filesystem>
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

    std::optional<std::string> tidyConfigFile;
    driver.cmdLine.add("--config-file", tidyConfigFile,
                       "Path to where the tidy config file is located");

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

    // Create the config class and populate it with the config file if provided
    TidyConfig tidyConfig;
    if (tidyConfigFile) {
        if (!exists(std::filesystem::path(tidyConfigFile.value())))
            slang::OS::printE(fmt::format("the path provided for the config file does not exist {}",
                                          tidyConfigFile.value()));
        tidyConfig = TidyConfigParser(tidyConfigFile.value()).getConfig();
    }

    // Print (short)descriptions of the checks
    if (printDescriptions || printShortDescriptions) {
        bool first = true;
        for (const auto& check_name : Registry::get_registered_checks()) {
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
        return 1;

    std::unique_ptr<ast::Compilation> compilation;
    bool compilation_ok;
    SLANG_TRY {
        compilation_ok = driver.parseAllSources();
        compilation = driver.createCompilation();
        compilation_ok &= driver.reportCompilation(*compilation, true);
    }
    SLANG_CATCH(const std::exception& e) {
#if __cpp_exceptions
        slang::OS::printE(fmt::format("internal compiler error: {}\n", e.what()));
#endif
        return 1;
    }

    if (!compilation_ok) {
        slang::OS::print("slang-tidy: errors found during compilation\n");
        return 1;
    }

    // Set the config to the Registry
    Registry::set_config(tidyConfig);

    DiagnosticEngine diagEngine(*compilation->getSourceManager());
    auto textDiagClient = std::make_shared<TextDiagnosticClient>();
    textDiagClient->showColors(true);
    diagEngine.addClient(textDiagClient);

    int ret_code = 0;

    // Check all enabled checks
    for (const auto& check_name : Registry::get_enabled_checks()) {
        const auto check = Registry::create(check_name);
        OS::print(fmt::format("[{}]", check->name()));

        diagEngine.setMessage(check->diagCode(), check->diagString());
        diagEngine.setSeverity(check->diagCode(), check->diagSeverity());

        auto checkOk = check->check(compilation->getRoot());
        if (!checkOk) {
            ret_code = 1;
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
