//------------------------------------------------------------------------------
// main.cpp
// Entry point for the primary driver program.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------

#include "compilation/Compilation.h"
#include "parsing/SyntaxTree.h"

#include <CLI/CLI.hpp>
#include <nlohmann/json.hpp>

using namespace slang;

bool runPreprocessor(SourceManager& sourceManager, const Bag& options,
                    const std::vector<SourceBuffer>& buffers) {
    BumpAllocator alloc;
    DiagnosticWriter writer(sourceManager);

    bool success = true;
    for (const SourceBuffer& buffer : buffers) {
        Diagnostics diagnostics;
        Preprocessor preprocessor(sourceManager, alloc, diagnostics, options);
        preprocessor.pushSource(buffer);

        SmallVectorSized<char, 32> output;
        while (true) {
            Token token = preprocessor.next();
            token.writeTo(output, SyntaxToStringFlags::IncludePreprocessed | SyntaxToStringFlags::IncludeTrivia);
            if (token.kind == TokenKind::EndOfFile)
                break;
        }

        if (diagnostics.empty())
            printf("%s:\n", std::string(sourceManager.getRawFileName(buffer.id)).c_str());
        else {
            printf("%s", writer.report(diagnostics).c_str());
            success = false;
        }

        printf("==============================\n%s\n", std::string(output.begin(), output.size()).c_str());
    }
    return success;
}

bool runCompiler(SourceManager& sourceManager, const Bag& options,
                 const std::vector<SourceBuffer>& buffers) {

    Compilation compilation;
    for (const SourceBuffer& buffer : buffers)
        compilation.addSyntaxTree(SyntaxTree::fromBuffer(buffer, sourceManager, options));

    Diagnostics diagnostics = compilation.getAllDiagnostics();
    DiagnosticWriter writer(sourceManager);
    printf("%s\n", writer.report(diagnostics).c_str());

    return diagnostics.empty();
}

int main(int argc, char** argv)
try {
    std::vector<std::string> sourceFiles;
    std::vector<std::string> includeDirs;
    std::vector<std::string> includeSystemDirs;
    std::vector<std::string> defines;
    std::vector<std::string> undefines;

    bool onlyPreprocess;

    CLI::App cmd("SystemVerilog compiler");
    cmd.add_option("files", sourceFiles, "Source files to compile");
    cmd.add_option("-I,--include-directory", includeDirs, "Additional include search paths");
    cmd.add_option("--include-system-directory", includeSystemDirs, "Additional system include search paths");
    cmd.add_option("-D,--define-macro", defines, "Define <macro>=<value> (or 1 if <value> ommitted) in all source files");
    cmd.add_option("-U,--undefine-macro", undefines, "Undefine macro name at the start of all source files");
    cmd.add_flag("-E,--preprocess", onlyPreprocess, "Only run the preprocessor (and print preprocessed files to stdout)");

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
            printf("error: no such file or directory: '%s'\n", file.c_str());
            anyErrors = true;
            continue;
        }

        buffers.push_back(buffer);
    }

    if (buffers.empty()) {
        printf("error: no input files\n");
        return 1;
    }

    if (onlyPreprocess)
        anyErrors |= !runPreprocessor(sourceManager, options, buffers);
    else
        anyErrors |= !runCompiler(sourceManager, options, buffers);

    return anyErrors ? 1 : 0;
}
catch (const std::exception& e) {
    printf("internal compiler error (exception): %s\n", e.what());
    return 2;
}