//------------------------------------------------------------------------------
// slang_main.cpp
// Entry point for the primary driver program.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include <fmt/color.h>
#include <fstream>
#include <iostream>

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/Json.h"
#include "slang/util/String.h"
#include "slang/util/TimeTrace.h"
#include "slang/util/Version.h"

using namespace slang;
using namespace slang::ast;
using namespace slang::driver;

void writeToFile(std::string_view fileName, std::string_view contents);

void printJson(Compilation& compilation, const std::string& fileName,
               const std::vector<std::string>& scopes) {
    JsonWriter writer;
    writer.setPrettyPrint(true);

    ASTSerializer serializer(compilation, writer);
    if (scopes.empty()) {
        serializer.serialize(compilation.getRoot());
    }
    else {
        for (auto& scopeName : scopes) {
            auto sym = compilation.getRoot().lookupName(scopeName);
            if (sym)
                serializer.serialize(*sym);
        }
    }

    writeToFile(fileName, writer.view());
}

template<typename TArgs>
int driverMain(int argc, TArgs argv) {
    SLANG_TRY {
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
        driver.cmdLine.add("-E,--preprocess", onlyPreprocess,
                           "Only run the preprocessor (and print preprocessed files to stdout)");
        driver.cmdLine.add("--macros-only", onlyMacros, "Print a list of found macros and exit");
        driver.cmdLine.add(
            "--parse-only", onlyParse,
            "Stop after parsing input files, don't perform elaboration or type checking");

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

        if (onlyParse.has_value() + onlyPreprocess.has_value() + onlyMacros.has_value() +
                driver.options.onlyLint.has_value() >
            1) {
            OS::printE(fg(driver.diagClient->errorColor), "error: ");
            OS::printE("can only specify one of --preprocess, --macros-only, "
                       "--parse-only, --lint-only");
            return 3;
        }

        if (timeTrace)
            TimeTrace::initialize();

        bool ok = true;
        SLANG_TRY {
            if (onlyPreprocess == true) {
                ok = driver.runPreprocessor(includeComments == true, includeDirectives == true,
                                            obfuscateIds == true);
            }
            else if (onlyMacros == true) {
                driver.reportMacros();
            }
            else if (onlyParse == true) {
                ok = driver.parseAllSources();
                ok &= driver.reportParseDiags();
            }
            else {
                {
                    TimeTraceScope timeScope("parseAllSources"sv, ""sv);
                    ok = driver.parseAllSources();
                }

                {
                    TimeTraceScope timeScope("elaboration"sv, ""sv);
                    auto compilation = driver.createCompilation();
                    ok &= driver.reportCompilation(*compilation, quiet == true);
                    if (astJsonFile)
                        printJson(*compilation, *astJsonFile, astJsonScopes);
                }
            }
        }
        SLANG_CATCH(const std::exception& e) {
#if __cpp_exceptions
            OS::printE(fmt::format("internal compiler error: {}\n", e.what()));
#endif
            return 4;
        }

        if (timeTrace) {
#if defined(_WIN32)
            std::ofstream file(widen(*timeTrace));
#else
            std::ofstream file(*timeTrace);
#endif
            TimeTrace::write(file);
            if (!file.flush()) {
                SLANG_THROW(std::runtime_error(
                    fmt::format("Unable to write time trace to '{}'", *timeTrace)));
            }
        }

        return ok ? 0 : 5;
    }
    SLANG_CATCH(const std::exception& e) {
#if __cpp_exceptions
        OS::printE(fmt::format("{}\n", e.what()));
#endif
        return 6;
    }
}

template<typename Stream, typename String>
void writeToFile(Stream& os, std::string_view fileName, String contents) {
    os.write(contents.data(), contents.size());
    os.flush();
    if (!os)
        SLANG_THROW(std::runtime_error(fmt::format("Unable to write AST to '{}'", fileName)));
}

#if defined(_WIN32)

void writeToFile(std::string_view fileName, std::string_view contents) {
    if (fileName == "-") {
        writeToFile(std::wcout, "stdout", widen(contents));
    }
    else {
        std::ofstream file(widen(fileName));
        writeToFile(file, fileName, contents);
    }
}

#    ifndef FUZZ_TARGET
int wmain(int argc, wchar_t** argv) {
    return driverMain(argc, argv);
}
#    endif

#else

void writeToFile(std::string_view fileName, std::string_view contents) {
    if (fileName == "-") {
        writeToFile(std::cout, "stdout", contents);
    }
    else {
        std::ofstream file{std::string(fileName)};
        writeToFile(file, fileName, contents);
    }
}

#    ifndef FUZZ_TARGET
int main(int argc, char** argv) {
    return driverMain(argc, argv);
}
#    endif

#endif

// When fuzzing with libFuzzer, this is the entry point.
#ifdef FUZZ_TARGET
extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
    auto& sourceManager = SyntaxTree::getDefaultSourceManager();

    std::string_view text(reinterpret_cast<const char*>(data), size);
    auto tree = SyntaxTree::fromFileInMemory(text, sourceManager);

    DiagnosticEngine diagEngine(sourceManager);
    auto diagClient = std::make_shared<TextDiagnosticClient>();
    diagEngine.addClient(diagClient);

    Compilation compilation;
    compilation.addSyntaxTree(tree);
    for (auto& diag : compilation.getAllDiagnostics())
        diagEngine.issue(diag);

    return 0;
}
#endif
