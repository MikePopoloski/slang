//------------------------------------------------------------------------------
// slang_main.cpp
// Entry point for the primary driver program.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include <fmt/color.h>
#include <fmt/ranges.h>
#include <fstream>
#include <iostream>

#include "slang/analysis/AnalysisManager.h"
#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/Driver.h"
#include "slang/text/Json.h"
#include "slang/util/TimeTrace.h"
#include "slang/util/VersionInfo.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::driver;

void printJson(Compilation& compilation, const std::string& fileName,
               const std::vector<std::string>& scopes, bool includeSourceInfo, bool detailedTypes) {
    JsonWriter writer;
    writer.setPrettyPrint(true);

    ASTSerializer serializer(compilation, writer);
    serializer.setIncludeSourceInfo(includeSourceInfo);
    serializer.setDetailedTypeInfo(detailedTypes);
    serializer.setTryConstantFold(false);

    if (scopes.empty()) {
        serializer.startObject();
        serializer.writeProperty("design");
        serializer.serialize(compilation.getRoot());
        serializer.writeProperty("definitions");
        serializer.startArray();
        for (auto def : compilation.getDefinitions())
            serializer.serialize(*def);
        serializer.endArray();
        serializer.endObject();
    }
    else {
        for (auto& scopeName : scopes) {
            auto sym = compilation.getRoot().lookupName(scopeName);
            if (sym)
                serializer.serialize(*sym);
        }
    }

    writer.writeNewLine();
    OS::writeFile(fileName, writer.view());
}

template<typename TArgs>
int driverMain(int argc, TArgs argv) {
    SLANG_TRY {
        OS::setupConsole();
        OS::tryEnableColors();

        Driver driver;
        driver.addStandardArgs();

        std::optional<bool> showHelp;
        std::optional<bool> showVersion;
        std::optional<bool> quiet;
        driver.cmdLine.add("-h,--help", showHelp, "Display available options");
        driver.cmdLine.add("--version", showVersion, "Display version information and exit");
        driver.cmdLine.add("-q,--quiet", quiet, "Suppress non-essential output");

        std::optional<bool> onlyPreprocess;
        std::optional<bool> onlyParse;
        std::optional<bool> onlyMacros;
        std::optional<bool> disableAnalysis;
        driver.cmdLine.add("-E,--preprocess", onlyPreprocess,
                           "Only run the preprocessor (and print preprocessed files to stdout)");
        driver.cmdLine.add("--macros-only", onlyMacros, "Print a list of found macros and exit");
        driver.cmdLine.add(
            "--parse-only", onlyParse,
            "Stop after parsing input files, don't perform elaboration or type checking");
        driver.cmdLine.add("--disable-analysis", disableAnalysis,
                           "Disables post-elaboration analysis passes,"
                           "which prevents some diagnostics from being issued");

        std::optional<bool> includeComments;
        std::optional<bool> includeDirectives;
        std::optional<bool> obfuscateIds;
        driver.cmdLine.add("--comments", includeComments,
                           "Include comments in preprocessed output (with -E)");
        driver.cmdLine.add("--directives", includeDirectives,
                           "Include compiler directives in preprocessed output (with -E)");
        driver.cmdLine.add("--obfuscate-ids", obfuscateIds,
                           "Randomize all identifiers in preprocessed output (with -E)");

        std::optional<std::string> astJsonFile;
        driver.cmdLine.add(
            "--ast-json", astJsonFile,
            "Dump the compiled AST in JSON format to the specified file, or '-' for stdout",
            "<file>", CommandLineFlags::FilePath);

        std::vector<std::string> astJsonScopes;
        driver.cmdLine.add("--ast-json-scope", astJsonScopes,
                           "When dumping AST to JSON, include only the scopes specified by the "
                           "given hierarchical paths",
                           "<path>");

        std::optional<bool> includeSourceInfo;
        driver.cmdLine.add("--ast-json-source-info", includeSourceInfo,
                           "When dumping AST to JSON, include source line and file information");

        std::optional<bool> serializeDetailedTypes;
        driver.cmdLine.add("--ast-json-detailed-types", serializeDetailedTypes,
                           "When dumping AST to JSON, expand out all type information");

        std::optional<std::string> depfileTarget;
        driver.cmdLine.add("--depfile-target", depfileTarget,
                           "Output depfile lists in makefile format, creating the file with "
                           "`<target>:` as the make target");

        std::optional<std::string> allDepfile;
        driver.cmdLine.add("--Mall,--all-deps", allDepfile,
                           "Generate dependency file list of all files used during parsing",
                           "<file>", CommandLineFlags::FilePath);

        std::optional<std::string> includeDepfile;
        driver.cmdLine.add(
            "--Minclude,--include-deps", includeDepfile,
            "Generate dependency file list of just include files that were used during parsing",
            "<file>", CommandLineFlags::FilePath);

        std::optional<std::string> moduleDepfile;
        driver.cmdLine.add(
            "--Mmodule,--module-deps", moduleDepfile,
            "Generate dependency file list of source files parsed, excluding include files",
            "<file>", CommandLineFlags::FilePath);

        std::optional<bool> depfileTrim;
        driver.cmdLine.add("--depfile-trim", depfileTrim,
                           "Trim unreferenced files before generating dependency lists");

        std::optional<std::string> timeTrace;
        driver.cmdLine.add("--time-trace", timeTrace,
                           "Do performance profiling of the slang compiler and output "
                           "the results to the given file in Chrome Event Tracing JSON format",
                           "<path>");

        if (!driver.parseCommandLine(argc, argv))
            return 1;

        if (showHelp == true) {
            OS::print(
                fmt::format("{}", driver.cmdLine.getHelpText("slang SystemVerilog compiler")));
            return 0;
        }

        if (showVersion == true) {
            OS::print(fmt::format("slang version {}.{}.{}+{}\n", VersionInfo::getMajor(),
                                  VersionInfo::getMinor(), VersionInfo::getPatch(),
                                  VersionInfo::getHash()));
            return 0;
        }

        if (!driver.processOptions())
            return 2;

        auto printError = [&](const std::string& message) {
            OS::printE(fg(driver.textDiagClient->errorColor), "error: ");
            OS::printE(message);
        };
        auto printWarning = [&](const std::string& message) {
            OS::printE(fg(driver.textDiagClient->warningColor), "warning: ");
            OS::printE(message);
        };

        if (onlyParse.has_value() + onlyPreprocess.has_value() + onlyMacros.has_value() +
                driver.options.lintMode() >
            1) {
            printError("can only specify one of --preprocess, --macros-only, "
                       "--parse-only, --lint-only");
            return 3;
        }

        if ((onlyPreprocess || onlyMacros) && (includeDepfile || moduleDepfile || allDepfile)) {
            printError("cannot use dependency file options with --preprocess or --macros-only");
            return 3;
        }

        if (timeTrace)
            TimeTrace::initialize();

        auto runStages = [&]() {
            bool ok = true;
            if (onlyPreprocess == true) {
                return driver.runPreprocessor(includeComments == true, includeDirectives == true,
                                              obfuscateIds == true);
            }

            if (onlyMacros == true) {
                driver.reportMacros();
                return true;
            }

            {
                TimeTraceScope timeScope("parseAllSources"sv, ""sv);
                ok = driver.parseAllSources();
            }
            if (depfileTrim == true) {
                DepTracker::DepResult result = driver.getReferencedDeps();
                // Since we're not elaborated, it's ok to have missing names
                if (!result.missingTops.empty()) {
                    printError(fmt::format("Top modules '{}' not found in source files",
                                           fmt::join(result.missingTops, ", ")));
                    ok = false;
                }
                if (!result.missingNames.empty()) {
                    printWarning(fmt::format("Referenced name(s) '{}' not found in source files",
                                             fmt::join(result.missingNames, ", ")));
                }

                if (includeDepfile) {
                    OS::writeFile(*includeDepfile,
                                  driver.serializeDepfiles(driver.getIncludePaths(result.depTrees),
                                                           includeDepfile));
                }
                if (moduleDepfile) {
                    std::vector<std::filesystem::path> moduleFiles;

                    auto paths = driver.getFilePaths(result.depTrees);

                    OS::writeFile(*moduleDepfile, driver.serializeDepfiles(paths, depfileTarget));
                }
                if (allDepfile) {
                    auto paths = driver.getIncludePaths(result.depTrees);

                    auto modulePaths = driver.getFilePaths(result.depTrees);
                    paths.insert(paths.end(), modulePaths.begin(), modulePaths.end());

                    OS::writeFile(*allDepfile, driver.serializeDepfiles(paths, depfileTarget));
                }
            }
            else {
                if (includeDepfile) {
                    OS::writeFile(*includeDepfile, driver.serializeDepfiles(
                                                       driver.getIncludePaths(), depfileTarget));
                }

                if (moduleDepfile) {
                    OS::writeFile(*moduleDepfile,
                                  driver.serializeDepfiles(driver.sourceLoader.getFilePaths(),
                                                           depfileTarget));
                }

                if (allDepfile) {
                    auto incPaths = driver.getIncludePaths();
                    auto paths = driver.sourceLoader.getFilePaths();
                    incPaths.insert(incPaths.end(), paths.begin(), paths.end());
                    OS::writeFile(*allDepfile, driver.serializeDepfiles(incPaths, depfileTarget));
                }
            }

            if (onlyParse == true)
                return ok && driver.reportParseDiags();

            std::unique_ptr<Compilation> compilation;
            {
                TimeTraceScope timeScope("elaboration"sv, ""sv);
                compilation = driver.createCompilation();
                driver.reportCompilation(*compilation, quiet == true);
            }

            if (!disableAnalysis.value_or(false)) {
                TimeTraceScope timeScope("semanticAnalysis"sv, ""sv);
                driver.runAnalysis(*compilation);
            }

            ok &= driver.reportDiagnostics(quiet == true);

            if (astJsonFile) {
                TimeTraceScope timeScope("serialization"sv, ""sv);
                printJson(*compilation, *astJsonFile, astJsonScopes, includeSourceInfo == true,
                          serializeDetailedTypes == true);
            }
            return ok;
        };

        bool ok = true;
        SLANG_TRY {
            ok = runStages();
        }
        SLANG_CATCH(const std::exception& e) {
            SLANG_REPORT_EXCEPTION(e, "internal compiler error: {}\n");
            return 4;
        }

        if (timeTrace) {
            std::ofstream file(*timeTrace);
            TimeTrace::write(file);
            if (!file.flush()) {
                SLANG_THROW(std::runtime_error(
                    fmt::format("Unable to write time trace to '{}'", *timeTrace)));
            }
        }

        return ok ? 0 : 5;
    }
    SLANG_CATCH(const std::exception& e) {
        SLANG_REPORT_EXCEPTION(e, "{}\n");
    }
    return 6;
}

#ifndef FUZZ_TARGET

int main(int argc, char** argv) {
    return driverMain(argc, argv);
}

#else

using namespace slang::syntax;

// When fuzzing with libFuzzer, this is the entry point.
extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
    SourceManager sourceManager;
    std::string_view text(reinterpret_cast<const char*>(data), size);
    auto tree = SyntaxTree::fromFileInMemory(text, sourceManager);

    DiagnosticEngine diagEngine(sourceManager);
    diagEngine.setErrorLimit(10);

    auto diagClient = std::make_shared<TextDiagnosticClient>();
    diagEngine.addClient(diagClient);

    CompilationOptions options;
    options.maxInstanceDepth = 16;
    options.maxDefParamSteps = 32;

    Compilation compilation(options);
    compilation.addSyntaxTree(tree);
    for (auto& diag : compilation.getAllDiagnostics())
        diagEngine.issue(diag);

    return 0;
}

#endif
