//------------------------------------------------------------------------------
// driver.cpp
// Entry point for the primary driver program.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/driver/Driver.h"

#include <fstream>
#include <iostream>

#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/Json.h"
#include "slang/util/Version.h"

#if defined(INCLUDE_SIM)
#    include "slang/codegen/JIT.h"
#    include "slang/mir/MIRBuilder.h"
#endif

using namespace slang;

void writeToFile(string_view fileName, string_view contents);

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

#if defined(INCLUDE_SIM)
using namespace slang::mir;

bool runSim(Compilation& compilation) {
    MIRBuilder builder(compilation);
    builder.elaborate();

    CodeGenerator codegen(compilation);
    codegen.emitAll(builder);

    JIT jit;
    jit.addCode(codegen.finish());
    return jit.run() == 0;
}
#endif

template<typename TArgs>
int driverMain(int argc, TArgs argv) try {
    OS::tryEnableColors();

    Driver driver;
    driver.addStandardArgs();

    optional<bool> showHelp;
    optional<bool> showVersion;
    optional<bool> quiet;
    driver.cmdLine.add("-h,--help", showHelp, "Display available options");
    driver.cmdLine.add("--version", showVersion, "Display version information and exit");
    driver.cmdLine.add("-q,--quiet", quiet, "Suppress non-essential output");

    optional<bool> onlyPreprocess;
    optional<bool> onlyParse;
    optional<bool> onlyMacros;
    driver.cmdLine.add("-E,--preprocess", onlyPreprocess,
                       "Only run the preprocessor (and print preprocessed files to stdout)");
    driver.cmdLine.add("--macros-only", onlyMacros, "Print a list of found macros and exit");
    driver.cmdLine.add(
        "--parse-only", onlyParse,
        "Stop after parsing input files, don't perform elaboration or type checking");

    optional<bool> includeComments;
    optional<bool> includeDirectives;
    driver.cmdLine.add("--comments", includeComments,
                       "Include comments in preprocessed output (with -E)");
    driver.cmdLine.add("--directives", includeDirectives,
                       "Include compiler directives in preprocessed output (with -E)");

    optional<std::string> astJsonFile;
    driver.cmdLine.add(
        "--ast-json", astJsonFile,
        "Dump the compiled AST in JSON format to the specified file, or '-' for stdout", "<file>",
        /* isFileName */ true);

    std::vector<std::string> astJsonScopes;
    driver.cmdLine.add("--ast-json-scope", astJsonScopes,
                       "When dumping AST to JSON, include only the scopes specified by the "
                       "given hierarchical paths",
                       "<path>");

#if defined(INCLUDE_SIM)
    optional<bool> shouldSim;
    driver.cmdLine.add("--sim", shouldSim, "After compiling, try to simulate the design");
#endif

    if (!driver.parseCommandLine(argc, argv))
        return 1;

    if (showHelp == true) {
        OS::print("{}", driver.cmdLine.getHelpText("slang SystemVerilog compiler"));
        return 0;
    }

    if (showVersion == true) {
        OS::print("slang version {}.{}.{}+{}\n", VersionInfo::getMajor(), VersionInfo::getMinor(),
                  VersionInfo::getPatch(), VersionInfo::getHash());
        return 0;
    }

    if (!driver.processOptions())
        return 2;

    if (onlyParse.has_value() + onlyPreprocess.has_value() + onlyMacros.has_value() +
            driver.options.onlyLint.has_value() >
        1) {
        OS::printE(fg(driver.diagClient->errorColor), "error: ");
        OS::printE(
            "can only specify one of --preprocess, --macros-only, --parse-only, --lint-only");
        return 3;
    }

    bool ok = true;
    try {
        if (onlyPreprocess == true) {
            ok = driver.runPreprocessor(includeComments == true, includeDirectives == true);
        }
        else if (onlyMacros == true) {
            driver.reportMacros();
        }
        else if (onlyParse == true) {
            ok = driver.parseAllSources();
            ok &= driver.reportParseDiags();
        }
        else {
            ok = driver.parseAllSources();

            auto compilation = driver.createCompilation();
            ok &= driver.reportCompilation(*compilation, quiet == true);

            if (astJsonFile)
                printJson(*compilation, *astJsonFile, astJsonScopes);

#if defined(INCLUDE_SIM)
            if (ok && shouldSim == true) {
                ok &= runSim(*compilation);
            }
#endif
        }
    }
    catch (const std::exception& e) {
        OS::printE("internal compiler error: {}\n", e.what());
        return 4;
    }

    return ok ? 0 : 5;
}
catch (const std::exception& e) {
    OS::printE("{}\n", e.what());
    return 6;
}

template<typename Stream, typename String>
void writeToFile(Stream& os, string_view fileName, String contents) {
    os.write(contents.data(), contents.size());
    os.flush();
    if (!os)
        throw std::runtime_error(fmt::format("Unable to write AST to '{}'", fileName));
}

#if defined(_MSC_VER)
#    include <Windows.h>

void writeToFile(string_view fileName, string_view contents) {
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

void writeToFile(string_view fileName, string_view contents) {
    if (fileName == "-") {
        writeToFile(std::cout, "stdout", contents);
    }
    else {
        std::ofstream file{ std::string(fileName) };
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

    string_view text(reinterpret_cast<const char*>(data), size);
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
