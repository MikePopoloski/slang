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

#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/Driver.h"
#include "slang/util/VersionInfo.h"

/// Performs a search for the .slang-tidy file on the current directory. If the file is not found,
/// tries on the parent directory until the root.
std::optional<std::filesystem::path> project_slang_tidy_config();
using namespace slang;

int main(int argc, char** argv) {
    OS::setupConsole();

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

    std::optional<bool> quietArg;
    driver.cmdLine.add("-q,--quiet", quietArg,
                       "slang-tidy will only print errors. Options that make slang-tidy print "
                       "information will not be affected by this.");
    std::optional<bool> superQuietArg;
    driver.cmdLine.add("--super-quiet", superQuietArg,
                       "slang-tidy will not print anything. Options that make slang-tidy print "
                       "information will not be affected by this.");

    std::optional<std::string> infoCode;
    driver.cmdLine.add("--code", infoCode, "print information about the error or warning.");

    if (!driver.parseCommandLine(argc, argv))
        return 1;

    bool superQuiet = superQuietArg.value_or(false);
    // slang-tidy on superQuiet mode, also implies being in quiet mode
    bool quiet = quietArg.value_or(false) || superQuiet;

    if (showHelp) {
        OS::print(fmt::format("{}", driver.cmdLine.getHelpText("slang SystemVerilog linter")));
        return 0;
    }

    if (showVersion) {
        OS::print(fmt::format("slang-tidy version {}.{}.{}+{}\n", VersionInfo::getMajor(),
                              VersionInfo::getMinor(), VersionInfo::getPatch(),
                              VersionInfo::getHash()));
        return 0;
    }

    if (infoCode) {
        // Create a sourceManage placeholder
        auto sm = SourceManager();
        Registry::setSourceManager(&sm);

        // Get the ID and kind from the check code string
        auto hypenPos = infoCode->find('-');
        if (hypenPos == std::string::npos) {
            OS::printE("Check code has not the correct format. Format should be ABCD-<id>\n");
            return 1;
        }
        auto kindStr = infoCode->substr(0, hypenPos);

        // Parse the ID and kind
        auto kind = tidyKindFromStr(kindStr);
        auto id = stoull(infoCode->substr(hypenPos + 1));

        if (!kind) {
            OS::printE(fmt::format("Check kind {} does not exist\n", kindStr));
            return 1;
        }

        for (const auto& checkName : Registry::getRegisteredChecks()) {
            const auto check = Registry::create(checkName);
            if (check->diagCode().getCode() == id && check->getKind() == kind) {
                OS::print(fmt::format(fmt::emphasis::bold, "[{}]\n", check->name()));
                OS::print(fmt::format("{}", check->description()));
                return 0;
            }
        }

        OS::printE(fmt::format("Check code {} does not exist\n", *infoCode));
        return 1;
    }

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

    // Create the config class and populate it with the config file if provided
    TidyConfig tidyConfig;
    if (tidyConfigFile) {
        if (!exists(std::filesystem::path(tidyConfigFile.value()))) {
            if (!superQuiet)
                OS::printE(fmt::format("the path provided for the config file does not exist {}",
                                       tidyConfigFile.value()));
            // Exit with error if the config file cannot be found
            return 1;
        }
        else {
            tidyConfig =
                TidyConfigParser(std::filesystem::path(tidyConfigFile.value())).getConfig();
        }
    }
    else if (auto path = project_slang_tidy_config()) {
        tidyConfig = TidyConfigParser(path.value()).getConfig();
    }

    // Add skipped files provided by the cmd args
    tidyConfig.addSkipFile(skippedFiles);

    // Add skipped paths provided by the cmd args
    tidyConfig.addSkipPath(skippedPaths);

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
        OS::printE(fmt::format("internal compiler error: {}\n", e.what()));
#endif
        return 1;
    }

    if (!compilationOk) {
        OS::printE("slang-tidy: errors found during compilation\n");
        return 1;
    }

    // Set the config to the Registry
    Registry::setConfig(tidyConfig);
    // Set the sourceManager to the Registry so checks can access it
    Registry::setSourceManager(compilation->getSourceManager());

    int retCode = 0;

    // Check all enabled checks
    auto& tdc = *driver.textDiagClient;
    for (const auto& checkName : Registry::getEnabledChecks()) {
        tdc.clear();

        const auto check = Registry::create(checkName);

        if (!quiet)
            OS::print(fmt::format("[{}]", check->name()));

        driver.diagEngine.setMessage(check->diagCode(), check->diagMessage());
        driver.diagEngine.setSeverity(check->diagCode(), check->diagSeverity());

        auto checkOk = check->check(compilation->getRoot());
        if (!checkOk) {
            retCode = 1;

            if (!quiet) {
                if (check->diagSeverity() == DiagnosticSeverity::Warning) {
                    OS::print(fmt::emphasis::bold |
                                  fmt::fg(tdc.getSeverityColor(DiagnosticSeverity::Warning)),
                              " WARN\n");
                }
                else if (check->diagSeverity() == DiagnosticSeverity::Error) {
                    OS::print(fmt::emphasis::bold |
                                  fmt::fg(tdc.getSeverityColor(DiagnosticSeverity::Error)),
                              " FAIL\n");
                }
                else {
                    SLANG_UNREACHABLE;
                }
            }

            if (!superQuiet) {
                for (const auto& diag : check->getDiagnostics()) {
                    driver.diagEngine.issue(diag);
                }
                OS::print(fmt::format("{}\n", tdc.getString()));
            }
        }
        else {
            if (!quiet)
                OS::print(fmt::emphasis::bold | fmt::fg(fmt::color::green), " PASS\n");
        }
    }

    return retCode;
}

/// Searches for a .slang-tidy file from the current path until the root '/'
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
