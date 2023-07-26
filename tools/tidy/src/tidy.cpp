//------------------------------------------------------------------------------
//! @file tidy.h
//! @brief A SystemVerilog linting tool
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

#include "slang/ast/Compilation.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/Driver.h"
#include "slang/util/Version.h"

/// Performs a search for the .slang-tidy file on the current directory. If the file is not found,
/// tries on the parent directory until the root.
std::optional<std::filesystem::path> project_slang_tidy_config();
using namespace slang;

int main(int argc, char** argv) {
    driver::Driver driver;
    driver.addStandardArgs();

    std::optional<bool> showHelp;
    std::optional<bool> showVersion;
    driver.cmdLine.add("-h,--help", showHelp, "Display available options");
    driver.cmdLine.add("--version", showVersion, "Display version information and exit");

    std::optional<bool> printDescriptions;
    std::optional<bool> printShortDescriptions;
    driver.cmdLine.add("--print-descriptions", printDescriptions,
                       "Displays the description of each check and exits");
    driver.cmdLine.add("--print-short-descriptions", printShortDescriptions,
                       "Displays the short description of each check and exits");

    std::optional<std::string> tidyConfigFile;
    driver.cmdLine.add("--config-file", tidyConfigFile,
                       "Path to where the tidy config file is located");

    std::vector<std::string> skippedFiles;
    driver.cmdLine.add("--skip-file", skippedFiles, "Files to be skipped by slang-tidy");

    std::vector<std::string> skippedPaths;
    driver.cmdLine.add("--skip-path", skippedPaths, "Paths to be skipped by slang-tidy");

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
    else if (auto path = project_slang_tidy_config()) {
        tidyConfig = TidyConfigParser(path.value()).getConfig();
    }

    // Add skipped files provided by the cmd args
    tidyConfig.addSkipFile(skippedFiles);

    // Add skipped paths provided by the cmd args
    tidyConfig.addSkipPath(skippedPaths);

    // Print (short)descriptions of the checks
    if (printDescriptions || printShortDescriptions) {
        // Create a sourceManage placeholder
        auto sm = SourceManager();
        Registry::setSourceManager(&sm);

        bool first = true;
        for (const auto& checkName : Registry::getRegisteredChecks()) {
            const auto check = Registry::create(checkName);
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
    bool compilationOk;
    SLANG_TRY {
        compilationOk = driver.parseAllSources();
        compilation = driver.createCompilation();
        compilationOk &= driver.reportCompilation(*compilation, true);
    }
    SLANG_CATCH(const std::exception& e) {
#if __cpp_exceptions
        slang::OS::printE(fmt::format("internal compiler error: {}\n", e.what()));
#endif
        return 1;
    }

    if (!compilationOk) {
        slang::OS::print("slang-tidy: errors found during compilation\n");
        return 1;
    }

    // Set the config to the Registry
    Registry::setConfig(tidyConfig);
    // Set the sourceManager to the Registry so checks can access it
    Registry::setSourceManager(compilation->getSourceManager());

    int retCode = 0;

    // Check all enabled checks
    for (const auto& checkName : Registry::getEnabledChecks()) {
        const auto check = Registry::create(checkName);
        OS::print(fmt::format("[{}]", check->name()));

        driver.diagEngine.setMessage(check->diagCode(), check->diagString());
        driver.diagEngine.setSeverity(check->diagCode(), check->diagSeverity());

        auto checkOk = check->check(compilation->getRoot());
        if (!checkOk) {
            retCode = 1;
            OS::print(fmt::emphasis::bold | fmt::fg(fmt::color::red), " FAIL\n");
            for (const auto& diag : check->getDiagnostics())
                driver.diagEngine.issue(diag);
            OS::print(fmt::format("{}\n", driver.diagClient->getString()));
            driver.diagClient->clear();
        }
        else {
            OS::print(fmt::emphasis::bold | fmt::fg(fmt::color::green), " PASS\n");
        }
    }

    return retCode;
}

std::optional<std::filesystem::path> project_slang_tidy_config() {
    std::optional<std::filesystem::path> ret = {};
    auto cwd = std::filesystem::current_path();
    while (cwd != cwd.root_path()) {
        if (exists(cwd / ".slang-tidy")) {
            ret = cwd / ".slang-tidy";
            break;
        }
        cwd = cwd.parent_path();
    }
    // Checks if the .slang-tidy is on the root path
    if (!ret.has_value() && exists(std::filesystem::path("/.slang-tidy"))) {
        ret = std::filesystem::path("/.slang-tidy");
    }
    return ret;
}
