//------------------------------------------------------------------------------
// driver.cpp
// Entry point for the primary driver program.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------

#include <fmt/format.h>
#include <nlohmann/json.hpp>

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"
#include "slang/util/CommandLine.h"
#include "slang/util/Version.h"

using namespace slang;

template<typename... Args>
void print(string_view format, const Args&... args);

void writeToFile(string_view fileName, string_view contents);

bool runPreprocessor(SourceManager& sourceManager, const Bag& options,
                     const std::vector<SourceBuffer>& buffers) {
    BumpAllocator alloc;

    bool success = true;
    for (const SourceBuffer& buffer : buffers) {
        Diagnostics diagnostics;
        Preprocessor preprocessor(sourceManager, alloc, diagnostics, options);
        preprocessor.pushSource(buffer);

        SyntaxPrinter output;
        while (true) {
            Token token = preprocessor.next();
            output.print(token);
            if (token.kind == TokenKind::EndOfFile)
                break;
        }

        if (diagnostics.empty())
            print("{}:\n", sourceManager.getRawFileName(buffer.id));
        else {
            print("{}", DiagnosticEngine::reportAll(sourceManager, diagnostics));
            success = false;
        }

        print("==============================\n{}\n", output.str());
    }
    return success;
}

bool runCompiler(SourceManager& sourceManager, const Bag& options,
                 const std::vector<SourceBuffer>& buffers,
                 const optional<std::string>& astJsonFile) {
    Compilation compilation;
    for (const SourceBuffer& buffer : buffers)
        compilation.addSyntaxTree(SyntaxTree::fromBuffer(buffer, sourceManager, options));

    DiagnosticEngine diagEngine(sourceManager);
    diagEngine.setIgnoreAllWarnings(true);

    auto client = std::make_shared<TextDiagnosticClient>();
    diagEngine.addClient(client);

    auto group = diagEngine.findDiagGroup("default"sv);
    ASSERT(group);
    diagEngine.setSeverity(*group, DiagnosticSeverity::Warning);

    for (auto& diag : compilation.getAllDiagnostics())
        diagEngine.issue(diag);

    print("{}", client->getString());

    if (astJsonFile) {
        json output = compilation.getRoot();
        writeToFile(*astJsonFile, output.dump(2));
    }

    return diagEngine.getNumErrors() == 0;
}

template<typename TArgs>
int driverMain(int argc, TArgs argv) try {
    std::vector<std::string> sourceFiles;
    std::vector<std::string> includeDirs;
    std::vector<std::string> includeSystemDirs;
    std::vector<std::string> defines;
    std::vector<std::string> undefines;

    optional<std::string> astJsonFile;

    optional<bool> showHelp;
    optional<bool> showVersion;
    optional<bool> onlyPreprocess;

    CommandLine cmdLine;
    cmdLine.add("-v,--version", showVersion, "Display version information and exit");
    cmdLine.add("-I", includeDirs, "Additional include search paths", "<dir>");
    cmdLine.add("--isystem", includeSystemDirs, "Additional system include search paths", "<dir>");
    cmdLine.add("-D", defines,
                "Define <macro> to <value> (or 1 if <value> ommitted) in all source files",
                "<macro>=<value>");
    cmdLine.add("-U", undefines, "Undefine macro name at the start of all source files", "<macro>");
    cmdLine.add("-E,--preprocess", onlyPreprocess,
                "Only run the preprocessor (and print preprocessed files to stdout)");
    cmdLine.add("--ast-json", astJsonFile,
                "Dump the compiled AST in JSON format to the specified file, or '-' for stdout",
                "<file>");
    cmdLine.add("-h,--help", showHelp, "Display available options");
    cmdLine.setPositional(sourceFiles, "files");

    if (!cmdLine.parse(argc, argv)) {
        for (auto& err : cmdLine.getErrors())
            print("{}\n", err);
        return 1;
    }

    if (showHelp == true) {
        print("{}", cmdLine.getHelpText("slang SystemVerilog compiler"));
        return 0;
    }

    if (showVersion == true) {
        print("slang version {}.{}.{}\n", VersionInfo::getMajor(), VersionInfo::getMinor(),
              VersionInfo::getRevision());
        return 0;
    }

    bool anyErrors = false;
    SourceManager sourceManager;
    for (const std::string& dir : includeDirs) {
        try {
            sourceManager.addUserDirectory(string_view(dir));
        }
        catch (const std::exception&) {
            print("error: include directory '{}' does not exist\n", dir);
            anyErrors = true;
        }
    }

    for (const std::string& dir : includeSystemDirs) {
        try {
            sourceManager.addSystemDirectory(string_view(dir));
        }
        catch (const std::exception&) {
            print("error: include directory '{}' does not exist\n", dir);
            anyErrors = true;
        }
    }

    PreprocessorOptions ppoptions;
    ppoptions.predefines = defines;
    ppoptions.undefines = undefines;
    ppoptions.predefineSource = "<command-line>";

    Bag options;
    options.add(ppoptions);

    std::vector<SourceBuffer> buffers;
    for (const std::string& file : sourceFiles) {
        SourceBuffer buffer = sourceManager.readSource(file);
        if (!buffer) {
            print("error: no such file or directory: '{}'\n", file);
            anyErrors = true;
            continue;
        }

        buffers.push_back(buffer);
    }

    if (anyErrors)
        return 2;

    if (buffers.empty()) {
        print("error: no input files\n");
        return 3;
    }

    try {
        if (onlyPreprocess == true)
            anyErrors = !runPreprocessor(sourceManager, options, buffers);
        else
            anyErrors = !runCompiler(sourceManager, options, buffers, astJsonFile);
    }
    catch (const std::exception& e) {
#ifdef FUZZ_TARGET
        (void)e;
        throw;
#else
        print("internal compiler error: {}\n", e.what());
        return 4;
#endif
    }

    return anyErrors ? 1 : 0;
}
catch (const std::exception& e) {
#ifdef FUZZ_TARGET
    (void)e;
    throw;
#else
    print("{}\n", e.what());
    return 5;
#endif
}

template<typename Stream, typename String>
void writeToFile(Stream& os, string_view fileName, String contents) {
    os.write(contents.data(), contents.size());
    os.flush();
    if (!os)
        throw std::runtime_error(fmt::format("Unable to write AST to '{}'", fileName));
}

#if defined(_MSC_VER)
#    include <fcntl.h>
#    include <fstream>
#    include <io.h>
#    include <iostream>

void writeToFile(string_view fileName, string_view contents) {
    if (fileName == "-") {
        writeToFile(std::wcout, "stdout", widen(contents));
    }
    else {
        std::ofstream file(widen(fileName));
        writeToFile(file, fileName, contents);
    }
}

template<typename T>
T convert(T&& t) {
    return std::forward<T>(t);
}

std::wstring convert(const std::string& s) {
    return widen(s);
}

std::wstring convert(const std::string_view& s) {
    return widen(s);
}

std::wstring convert(const char* s) {
    return widen(s);
}

template<typename... Args>
void print(string_view format, const Args&... args) {
    fmt::vprint(widen(format), fmt::make_format_args<fmt::wformat_context>(convert(args)...));
}

int wmain(int argc, wchar_t** argv) {
    _setmode(_fileno(stdout), _O_U16TEXT);
    return driverMain(argc, argv);
}

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

template<typename... Args>
void print(string_view format, const Args&... args) {
    fmt::vprint(format, fmt::make_format_args(args...));
}

int main(int argc, char** argv) {
    return driverMain(argc, argv);
}

#endif