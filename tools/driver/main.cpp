//------------------------------------------------------------------------------
// main.cpp
// Entry point for the primary driver program.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------

#include "compilation/Compilation.h"
#include "parsing/SyntaxTree.h"

#include "CLI11.hpp"
#include "json.hpp"

using namespace slang;

int main(int argc, char** argv)
try {
    std::vector<std::string> sourceFiles;

    CLI::App cmd("SystemVerilog compiler");
    cmd.add_option("files", sourceFiles, "Source files to compile");

    try {
        cmd.parse(argc, argv);
    }
    catch (const CLI::ParseError& e) {
        return cmd.exit(e);
    }

    // Initialize the source manager.
    SourceManager sourceManager;

    // Build the compilation out of each source file.
    Compilation compilation;
    bool anyErrors = false;
    for (const std::string& file : sourceFiles) {
        std::shared_ptr<SyntaxTree> tree = SyntaxTree::fromFile(file, sourceManager);
        if (!tree) {
            printf("error: no such file or directory: '%s'\n", file.c_str());
            anyErrors = true;
            continue;
        }

        compilation.addSyntaxTree(std::move(tree));
    }

    if (compilation.getSyntaxTrees().empty()) {
        printf("error: no input files\n");
        return 1;
    }

    // Report diagnostics.
    Diagnostics diagnostics = compilation.getAllDiagnostics();
    DiagnosticWriter writer(sourceManager);
    printf("%s\n", writer.report(diagnostics).c_str());

    return !anyErrors && diagnostics.empty() ? 0 : 1;
}
catch (const std::exception& e) {
    printf("internal compiler error (exception): %s\n", e.what());
    return 2;
}