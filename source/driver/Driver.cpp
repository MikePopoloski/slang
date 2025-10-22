//------------------------------------------------------------------------------
// Driver.cpp
// Driver implementation with reporting and output functionality for CLI tools
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/driver/Driver.h"

#include <fmt/color.h>
#include <memory>

#include "slang/analysis/AnalysisManager.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/diagnostics/DiagnosticClient.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/JsonDiagnosticClient.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/BaseDriver.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/FormatBuffer.h"
#include "slang/text/Json.h"
#include "slang/util/OS.h"
#include "slang/util/Random.h"

namespace fs = std::filesystem;

namespace slang::driver {

using namespace ast;
using namespace parsing;
using namespace syntax;
using namespace analysis;

Driver::Driver() : ClientOwningDriver<TextDiagnosticClient>() {
    textDiagClient = this->diagClient;
}

Driver::~Driver() = default;

void Driver::addStandardArgs() {
    // Call base class to add core arguments
    BaseDriver::addStandardArgs();

    // Diagnostics control
    cmdLine.add("--color-diagnostics", diagFormatOptions.colorDiags,
                "Always print diagnostics in color. "
                "If this option is unset, colors will be enabled if a color-capable "
                "terminal is detected.");
    cmdLine.add("--diag-column", diagFormatOptions.diagColumn,
                "Show column numbers in diagnostic output");
    cmdLine.addEnum<ColumnUnit, ColumnUnit_traits>("--diag-column-unit",
                                                   diagFormatOptions.diagColumnUnit,
                                                   "Unit for column numbers in diagnostics",
                                                   "<unit>");
    cmdLine.add("--diag-location", diagFormatOptions.diagLocation,
                "Show location information in diagnostic output");
    cmdLine.add("--diag-source", diagFormatOptions.diagSourceLine,
                "Show source line or caret info in diagnostic output");
    cmdLine.add("--diag-option", diagFormatOptions.diagOptionName,
                "Show option names in diagnostic output");
    cmdLine.add("--diag-include-stack", diagFormatOptions.diagIncludeStack,
                "Show include stacks in diagnostic output");
    cmdLine.add("--diag-macro-expansion", diagFormatOptions.diagMacroExpansion,
                "Show macro expansion backtraces in diagnostic output");
    cmdLine.add("--diag-abs-paths", diagFormatOptions.diagAbsPaths,
                "Display absolute paths to files in diagnostic output");
    cmdLine.addEnum<ShowHierarchyPathOption, ShowHierarchyPathOption_traits>(
        "--diag-hierarchy", diagFormatOptions.diagHierarchy,
        "Show hierarchy locations in diagnostic output", "always|never|auto");
    cmdLine.add("--diag-json", diagFormatOptions.diagJson,
                "Dump all diagnostics in JSON format to the specified file, or '-' for stdout",
                "<file>", CommandLineFlags::FilePath);

    // Dependency files
    cmdLine.add("--depfile-target", depFileOptions.depfileTarget,
                "Output depfile lists in makefile format, creating the file with "
                "`<target>:` as the make target");
    cmdLine.add("--Mall,--all-deps", depFileOptions.allDepfile,
                "Generate dependency file list of all files used during parsing", "<file>",
                CommandLineFlags::FilePath);
    cmdLine.add("--Minclude,--include-deps", depFileOptions.includeDepfile,
                "Generate dependency file list of just include files that were "
                "used during parsing",
                "<file>", CommandLineFlags::FilePath);
    cmdLine.add("--Mmodule,--module-deps", depFileOptions.moduleDepfile,
                "Generate dependency file list of source files parsed, excluding include files",
                "<file>", CommandLineFlags::FilePath);
    cmdLine.add("--depfile-trim", depFileOptions.depfileTrim,
                "Trim unreferenced files before generating dependency lists "
                "(also implies --depfile-sort)");
    cmdLine.add("--depfile-sort", depFileOptions.depfileSort,
                "Topologically sort the emitted files in dependency lists");
}

bool Driver::processOptions() {
    // Set up diagnostic client configuration
    bool showColors;
    if (diagFormatOptions.colorDiags.has_value())
        showColors = *diagFormatOptions.colorDiags;
    else
        showColors = OS::fileSupportsColors(stderr);

    if (showColors) {
        OS::setStderrColorsEnabled(true);
        if (OS::fileSupportsColors(stdout))
            OS::setStdoutColorsEnabled(true);
    }

    if (diagFormatOptions.diagJson.has_value()) {
        jsonWriter = std::make_unique<JsonWriter>();
        jsonWriter->setPrettyPrint(true);
        jsonWriter->startArray();

        jsonDiagClient = std::make_shared<JsonDiagnosticClient>(*jsonWriter);
        jsonDiagClient->showAbsPaths(diagFormatOptions.diagAbsPaths.value_or(false));
        jsonDiagClient->setColumnUnit(
            diagFormatOptions.diagColumnUnit.value_or(ColumnUnit::Display));
        diagEngine.addClient(jsonDiagClient);
    }

    if (!BaseDriver::processOptions())
        return false;

    auto& tdc = *textDiagClient;
    tdc.showColors(showColors);
    tdc.showColumn(diagFormatOptions.diagColumn.value_or(true));
    tdc.setColumnUnit(diagFormatOptions.diagColumnUnit.value_or(ColumnUnit::Display));
    tdc.showLocation(diagFormatOptions.diagLocation.value_or(true));
    tdc.showSourceLine(diagFormatOptions.diagSourceLine.value_or(true));
    tdc.showOptionName(diagFormatOptions.diagOptionName.value_or(true));
    tdc.showIncludeStack(diagFormatOptions.diagIncludeStack.value_or(true));
    tdc.showMacroExpansion(diagFormatOptions.diagMacroExpansion.value_or(true));
    tdc.showAbsPaths(diagFormatOptions.diagAbsPaths.value_or(false));
    tdc.showHierarchyInstance(
        diagFormatOptions.diagHierarchy.value_or(ShowHierarchyPathOption::Auto));

    return true;
}

template<typename TGenerator>
static std::string generateRandomAlphaString(TGenerator& gen, size_t len) {
    static constexpr auto chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                                  "abcdefghijklmnopqrstuvwxyz"sv;
    auto result = std::string(len, '\0');
    std::ranges::generate_n(begin(result), ptrdiff_t(len), [&] {
        return chars[getUniformIntDist(gen, size_t(0), chars.size() - 1)];
    });
    return result;
}

bool Driver::runPreprocessor(bool includeComments, bool includeDirectives, bool obfuscateIds,
                             bool useFixedObfuscationSeed) {
    BumpAllocator alloc;
    Diagnostics diagnostics;
    Preprocessor preprocessor(sourceManager, alloc, diagnostics, createParseOptionBag());

    auto buffers = sourceLoader.loadSources();
    for (auto it = buffers.rbegin(); it != buffers.rend(); it++)
        preprocessor.pushSource(*it);

    SyntaxPrinter output;
    output.setIncludeComments(includeComments);
    output.setIncludeDirectives(includeDirectives);

    std::optional<std::mt19937> rng;
    flat_hash_map<std::string, std::string> obfuscationMap;

    if (obfuscateIds) {
        if (useFixedObfuscationSeed)
            rng.emplace();
        else
            rng = createRandomGenerator<std::mt19937>();
    }

    while (true) {
        Token token = preprocessor.next();
        if (token.kind == TokenKind::IntegerBase) {
            // This is needed for the case where obfuscation is enabled,
            // the digits of a vector literal may be lexed initially as
            // an identifier and we don't have the parser here to fix things
            // up for us.
            do {
                output.print(token);
                token = preprocessor.next();
            } while (SyntaxFacts::isPossibleVectorDigit(token.kind));
        }

        if (obfuscateIds && token.kind == TokenKind::Identifier) {
            auto name = std::string(token.valueText());
            auto translation = obfuscationMap.find(name);
            if (translation == obfuscationMap.end()) {
                auto newName = generateRandomAlphaString(*rng, 16);
                translation = obfuscationMap.emplace(name, newName).first;
            }
            token = token.withRawText(alloc, translation->second);
        }

        output.print(token);
        if (token.kind == TokenKind::EndOfFile)
            break;
    }

    // Only print diagnostics if actual errors occurred.
    for (auto& diag : diagnostics) {
        if (diag.isError()) {
            OS::printE(fmt::format("{}", DiagnosticEngine::reportAll(sourceManager, diagnostics)));
            return false;
        }
    }

    OS::print(fmt::format("{}\n", output.str()));
    return true;
}

void Driver::reportMacros() {
    Bag optionBag;
    addParseOptions(optionBag);

    BumpAllocator alloc;
    Diagnostics diagnostics;
    Preprocessor preprocessor(sourceManager, alloc, diagnostics, optionBag);

    auto buffers = sourceLoader.loadSources();
    for (auto it = buffers.rbegin(); it != buffers.rend(); it++)
        preprocessor.pushSource(*it);

    while (true) {
        Token token = preprocessor.next();
        if (token.kind == TokenKind::EndOfFile)
            break;
    }

    for (auto macro : preprocessor.getDefinedMacros()) {
        SyntaxPrinter printer;
        printer.setIncludeComments(false);
        printer.setIncludeTrivia(false);
        printer.print(macro->name);

        printer.setIncludeTrivia(true);
        if (macro->formalArguments)
            printer.print(*macro->formalArguments);

        if (!macro->body.empty() && macro->body[0].trivia().empty())
            printer.append(" "sv);

        printer.print(macro->body);

        OS::print(fmt::format("{}\n", printer.str()));
    }
}

void Driver::optionallyWriteDepFiles() {
    if (!depFileOptions.includeDepfile && !depFileOptions.moduleDepfile &&
        !depFileOptions.allDepfile)
        return;

    std::vector<const SyntaxTree*> depTrees;
    if (depFileOptions.depfileTrim == true || depFileOptions.depfileSort == true) {
        depTrees = getSortedDependencies(*this, syntaxTrees, depFileOptions.depfileTrim == true);
    }
    else {
        depTrees.reserve(syntaxTrees.size());
        for (auto& tree : syntaxTrees)
            depTrees.push_back(tree.get());
    }

    auto writeDepFile = [&](const std::vector<std::string>& paths, std::string_view fileName) {
        FormatBuffer buffer;
        if (depFileOptions.depfileTarget)
            buffer.format("{}: ", *depFileOptions.depfileTarget);

        for (auto& path : paths) {
            buffer.append(path);

            // If depfileTarget is provided the delimiter is a space, otherwise a newline.
            if (depFileOptions.depfileTarget)
                buffer.append(" ");
            else
                buffer.append("\n");
        }

        if (depFileOptions.depfileTarget) {
            buffer.pop_back();
            buffer.append("\n");
        }

        OS::writeFile(fileName, buffer.str());
    };

    std::vector<std::string> includePaths;
    flat_hash_set<fs::path> seenPaths;
    if (depFileOptions.includeDepfile || depFileOptions.allDepfile) {
        for (auto& tree : depTrees) {
            for (auto& inc : tree->getIncludeDirectives()) {
                if (inc.isSystem)
                    continue;

                auto p = sourceManager.getFullPath(inc.buffer.id);
                if (seenPaths.insert(p).second)
                    includePaths.emplace_back(getProximatePathStr(p));
            }
        }

        if (depFileOptions.includeDepfile)
            writeDepFile(includePaths, *depFileOptions.includeDepfile);
    }

    std::vector<std::string> modulePaths;
    if (depFileOptions.moduleDepfile || depFileOptions.allDepfile) {
        for (auto& tree : depTrees) {
            for (auto bufferId : tree->getSourceBufferIds()) {
                auto path = sourceManager.getFullPath(bufferId);
                if (!path.empty())
                    modulePaths.emplace_back(getProximatePathStr(path));
            }
        }

        if (depFileOptions.moduleDepfile)
            writeDepFile(modulePaths, *depFileOptions.moduleDepfile);
    }

    if (depFileOptions.allDepfile) {
        includePaths.insert(includePaths.end(), modulePaths.begin(), modulePaths.end());
        writeDepFile(includePaths, *depFileOptions.allDepfile);
    }
}
bool Driver::reportParseDiags() {
    Diagnostics diags;
    for (auto& tree : sourceLoader.getLibraryMaps())
        diags.append_range(tree->diagnostics());
    for (auto& tree : syntaxTrees)
        diags.append_range(tree->diagnostics());

    diags.sort(sourceManager);
    for (auto& diag : diags)
        diagEngine.issue(diag);

    OS::printE(fmt::format("{}", textDiagClient->getString()));
    return diagEngine.getNumErrors() == 0;
}

void Driver::reportCompilation(Compilation& compilation, bool quiet) {
    if (!quiet) {
        auto topInstances = compilation.getRoot().topInstances;
        if (!topInstances.empty()) {
            OS::print(fg(textDiagClient->warningColor), "Top level design units:\n");
            for (auto inst : topInstances)
                OS::print(fmt::format("    {}\n", inst->name));
            OS::print("\n");
        }
    }

    for (auto& diag : compilation.getAllDiagnostics())
        diagEngine.issue(diag);
}

bool Driver::reportDiagnostics(bool quiet) {
    bool hasDiagsStdout = false;
    bool succeeded = diagEngine.getNumErrors() == 0;

    if (jsonWriter)
        jsonWriter->endArray();

    if (diagFormatOptions.diagJson == "-") {
        // If we're printing JSON diagnostics to stdout don't also
        // print the text diagnostics.
        hasDiagsStdout = true;
        OS::print(jsonWriter->view());
    }
    else {
        std::string diagStr = textDiagClient->getString();
        hasDiagsStdout = diagStr.size() > 1;
        OS::printE(diagStr);

        if (jsonWriter)
            OS::writeFile(*diagFormatOptions.diagJson, jsonWriter->view());
    }

    if (!quiet) {
        if (hasDiagsStdout)
            OS::print("\n");

        if (succeeded)
            OS::print(fg(textDiagClient->highlightColor), "Build succeeded: ");
        else
            OS::print(fg(textDiagClient->errorColor), "Build failed: ");

        OS::print(fmt::format("{} error{}, {} warning{}\n", diagEngine.getNumErrors(),
                              diagEngine.getNumErrors() == 1 ? "" : "s",
                              diagEngine.getNumWarnings(),
                              diagEngine.getNumWarnings() == 1 ? "" : "s"));
    }

    return succeeded;
}

bool Driver::runFullCompilation(bool quiet) {
    auto compilation = createCompilation();
    reportCompilation(*compilation, quiet);
    runAnalysis(*compilation);
    return reportDiagnostics(quiet);
}

} // namespace slang::driver
