//------------------------------------------------------------------------------
//! @file reflect.cpp
//! @brief Generates C++ headers for SystemVerilog types
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "ASTVisitors.h"
#include "SvTypeReflector.h"
#include <fmt/format.h>
#include <iostream>
#include <optional>

#include "slang/driver/Driver.h"
#include "slang/util/VersionInfo.h"

using namespace slang;

int main(int argc, char** argv) {
    OS::setupConsole();

    driver::Driver driver;
    driver.addStandardArgs();
    std::optional<bool> showHelp;
    driver.cmdLine.add("-h,--help", showHelp, "Display available options");
    std::optional<bool> showVersion;
    driver.cmdLine.add("--version", showVersion, "Display version information and exit");
    std::optional<std::string> outputDir;
    driver.cmdLine.add("--output-dir", outputDir, "Output directory of the generated .h files");
    std::optional<bool> toStdout;
    driver.cmdLine.add("--stdout", toStdout, "Prints output in the stdout");
    std::optional<bool> verbose;
    driver.cmdLine.add("--verbose", verbose, "Outputs information about the process");
    std::optional<bool> noSystemC;
    driver.cmdLine.add(
        "--no-sc", noSystemC,
        "Doesn't use SystemC types to generate the headers. Will fail if some public type "
        "can not be made public without SystemC support");

    if (!driver.parseCommandLine(argc, argv))
        return 1;

    if (showHelp) {
        OS::print(fmt::format("{}", driver.cmdLine.getHelpText("slang-reflect")));
        return 0;
    }

    if (showVersion) {
        OS::print(fmt::format("slang-reflect version {}.{}.{}+{}\n", VersionInfo::getMajor(),
                              VersionInfo::getMinor(), VersionInfo::getPatch(),
                              VersionInfo::getHash()));
        return 0;
    }

    const bool info = verbose && *verbose;

    fs::path outputPath = ".";
    if (outputDir && !toStdout) {
        outputPath = *outputDir;
        if (!is_directory(outputPath)) {
            OS::printE("Path is not a directory: " + outputPath.string());
            return 1;
        }
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
        OS::printE(fmt::format("internal compiler error: {}\n", e.what()));
#endif
        return 1;
    }

    if (!compilation_ok) {
        OS::print("slang-reflect: errors found during compilation\n");
        return 1;
    }

    const bool noSc = noSystemC.has_value() && noSystemC.value();

    auto reflector = SvTypeReflector(std::move(compilation), info, noSc);
    reflector.reflect();

    if (toStdout && *toStdout) {
        std::cout << reflector.emit() << '\n';
    }
    else {
        OS::print("Emitting code to: " + absolute(outputPath).string() + "\n");
        reflector.emitToFile(outputPath);
    }
}
