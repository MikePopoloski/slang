//------------------------------------------------------------------------------
// driver.cpp
// Entry point for the primary driver program.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------

#include <CLI/CLI.hpp>
#include <fmt/format.h>
#include <nlohmann/json.hpp>

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DiagnosticWriter.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"

using namespace slang;

template<typename... Args>
void print(string_view format, const Args&... args);

void writeToFile(string_view fileName, string_view contents);

bool runPreprocessor(SourceManager& sourceManager, const Bag& options,
                     const std::vector<SourceBuffer>& buffers) {
    BumpAllocator alloc;
    DiagnosticWriter writer(sourceManager);

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
            print("{}", writer.report(diagnostics));
            success = false;
        }

        print("==============================\n{}\n", output.str());
    }
    return success;
}

bool runCompiler(SourceManager& sourceManager, const Bag& options,
                 const std::vector<SourceBuffer>& buffers, const std::string& astJsonFile) {
    Compilation compilation;
    for (const SourceBuffer& buffer : buffers)
        compilation.addSyntaxTree(SyntaxTree::fromBuffer(buffer, sourceManager, options));

    auto& diagnostics = compilation.getAllDiagnostics();
    DiagnosticWriter writer(sourceManager);
    print("{}", writer.report(diagnostics));

    if (!astJsonFile.empty()) {
        json output = compilation.getRoot();
        writeToFile(astJsonFile, output.dump(2));
    }

    return diagnostics.empty();
}

int driverMain(int argc, char** argv) try {
    std::vector<std::string> sourceFiles;
    std::vector<std::string> includeDirs;
    std::vector<std::string> includeSystemDirs;
    std::vector<std::string> defines;
    std::vector<std::string> undefines;

    std::string astJsonFile;

    bool onlyPreprocess;

    CLI::App cmd("SystemVerilog compiler");
    cmd.add_option("files", sourceFiles, "Source files to compile");
    cmd.add_option("-I,--include-directory", includeDirs, "Additional include search paths");
    cmd.add_option("--include-system-directory", includeSystemDirs,
                   "Additional system include search paths");
    cmd.add_option("-D,--define-macro", defines,
                   "Define <macro>=<value> (or 1 if <value> ommitted) in all source files");
    cmd.add_option("-U,--undefine-macro", undefines,
                   "Undefine macro name at the start of all source files");
    cmd.add_flag("-E,--preprocess", onlyPreprocess,
                 "Only run the preprocessor (and print preprocessed files to stdout)");

    cmd.add_option("--ast-json", astJsonFile,
                   "Dump the compiled AST in JSON format to the specified file, or '-' for stdout");

    try {
        cmd.parse(argc, argv);
    }
    catch (const CLI::ParseError& e) {
        return cmd.exit(e);
    }

    SourceManager sourceManager;
    for (const std::string& dir : includeDirs)
        sourceManager.addUserDirectory(string_view(dir));

    for (const std::string& dir : includeSystemDirs)
        sourceManager.addSystemDirectory(string_view(dir));

    PreprocessorOptions ppoptions;
    ppoptions.predefines = defines;
    ppoptions.undefines = undefines;
    ppoptions.predefineSource = "<command-line>";

    Bag options;
    options.add(ppoptions);

    bool anyErrors = false;
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
        return 1;

    if (buffers.empty()) {
        print("error: no input files\n");
        return 2;
    }

    try {
        if (onlyPreprocess)
            anyErrors = !runPreprocessor(sourceManager, options, buffers);
        else
            anyErrors = !runCompiler(sourceManager, options, buffers, astJsonFile);
    }
    catch (const std::exception& e) {
#ifdef FUZZ_TARGET
        throw;
#else
        print("internal compiler error: {}\n", e.what());
        return 3;
#endif
    }

    return anyErrors ? 1 : 0;
}
catch (const std::exception& e) {
#ifdef FUZZ_TARGET
    throw;
#else
    print("{}\n", e.what());
    return 4;
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
#    include <io.h>

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

    std::vector<std::string> storage;
    std::vector<char*> utf8Argv;

    storage.reserve(argc);
    utf8Argv.reserve(argc);

    for (int i = 0; i < argc; ++i) {
        storage.emplace_back(narrow(argv[i]));
        utf8Argv.push_back(storage.back().data());
    }

    return driverMain(argc, utf8Argv.data());
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