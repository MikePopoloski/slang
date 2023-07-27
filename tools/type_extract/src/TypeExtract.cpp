//------------------------------------------------------------------------------
//! @file type_extract.h
//! @brief A SystemVerilog linting tool
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include "ASTVisitors.h"
#include "SvTypeExtractor.h"
#include <fmt/format.h>
#include <optional>

#include "slang/driver/Driver.h"

using namespace slang;

int main(int argc, char** argv) {
    driver::Driver driver;
    driver.addStandardArgs();
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

    if (!driver.processOptions())
        return 1;

    bool info = verbose && *verbose;

    fs::path outputPath = ".";
    if (outputDir && !toStdout) {
        outputPath = *outputDir;
        if (!is_directory(outputPath)) {
            OS::printE("Path is not a directory: " + outputPath.string());
            return 1;
        }
    }

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
        OS::print("slang-tidy: errors found during compilation\n");
        return 1;
    }

    bool noSc = noSystemC.has_value() && noSystemC.value();

    auto extractor = SvTypeExtractor(std::move(compilation), info, noSc);
    extractor.extract();

    if (toStdout && *toStdout) {
        std::cout << extractor.emit() << std::endl;
    }
    else {
        OS::print("Emitting code to: " + absolute(outputPath).string() + "\n");
        extractor.emitToFile(outputPath);
    }
}
