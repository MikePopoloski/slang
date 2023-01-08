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

    std::optional<bool> disableSynthesisChecks;
    driver.cmdLine.add("--disable-synthesis-checks", disableSynthesisChecks,
                       "Disables the synthesis checks");

    std::optional<bool> onlySynthesisChecks;
    driver.cmdLine.add("--only-synthesis-checks", onlySynthesisChecks,
                       "Disables the synthesis checks");

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

    std::unordered_set<slang::TidyKind> disabledChecks;
    if (disableSynthesisChecks)
        disabledChecks.insert(TidyKind::Synthesis);

    auto filter_func = [&](const Registry::RegistryItem& item){
        if (disabledChecks.count(item.second.kind))
            return false;
        if (onlySynthesisChecks)
            return item.second.kind == slang::TidyKind::Synthesis;
        return true;
    };

    for (const auto& check_name : Registry::get_registered(filter_func)) {
        const auto check = Registry::create(check_name);
        OS::print(fmt::format("slang-tidy: [{}]", check->name()));

        diagEngine.setMessage(check->diagCode(), check->diagString());
        diagEngine.setSeverity(check->diagCode(), check->diagSeverity());

        auto checkOk = check->check(compilation->getRoot());
        if (!checkOk) {
            OS::print("\n");
            const auto& diags = check->getDiagnostics();
            for (const auto& diag : diags)
                diagEngine.issue(diag);
            OS::print(fmt::format("{}\n", textDiagClient->getString()));
            textDiagClient->clear();
        }
        else {
            OS::print(fmt::emphasis::bold | fmt::fg(fmt::color::green), " OK\n");
        }
    }

    return 0;
}
