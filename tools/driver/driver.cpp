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
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"

using namespace slang;

void writeToFile(const std::string& fileName, const std::string& contents) {
    auto onError = [&]() {
        throw fmt::system_error(errno, "Unable to write AST to '{}'", fileName);
    };

    FILE* fp;
    if (fileName == "-")
        fp = stdout;
    else {
        fp = fopen(fileName.c_str(), "w");
        if (!fp)
            onError();
    }

    int rc = fputs(contents.c_str(), fp);
    if (rc == EOF)
        onError();

    if (fp != stdout)
        fclose(fp);
}

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
            fmt::print("{}:\n", sourceManager.getRawFileName(buffer.id));
        else {
            fmt::print("%s", writer.report(diagnostics));
            success = false;
        }

        fmt::print("==============================\n{}\n", output.str());
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
    fmt::print("{}", writer.report(diagnostics));

    if (!astJsonFile.empty()) {
        json output;
        to_json(output, compilation.getRoot());
        writeToFile(astJsonFile, output.dump(2));
    }

    return diagnostics.empty();
}

int main(int argc, char** argv) try {
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
            fmt::print("error: no such file or directory: '{}'\n", file);
            anyErrors = true;
            continue;
        }

        buffers.push_back(buffer);
    }

    if (buffers.empty()) {
        puts("error: no input files\n");
        return 1;
    }

    try {
        if (onlyPreprocess)
            anyErrors |= !runPreprocessor(sourceManager, options, buffers);
        else
            anyErrors |= !runCompiler(sourceManager, options, buffers, astJsonFile);
    }
    catch (const std::exception& e) {
        fmt::print("internal compiler error: {}\n", e.what());
        return 2;
    }

    return anyErrors ? 1 : 0;
}
catch (const std::exception& e) {
    fmt::print("{}\n", e.what());
    return 3;
}