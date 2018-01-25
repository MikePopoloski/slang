//------------------------------------------------------------------------------
// main.cpp
// Entry point for the primary driver program.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------

#include "compilation/Compilation.h"
#include "parsing/SyntaxTree.h"

#include "CLI11.hpp"

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
    for (const std::string& file : sourceFiles)
        compilation.addSyntaxTree(SyntaxTree::fromFile(file, sourceManager));

    // Report diagnostics.
    Diagnostics diagnostics = compilation.getAllDiagnostics();
    DiagnosticWriter writer(sourceManager);
    printf("%s\n", writer.report(diagnostics).c_str());

    return 0;
}
catch (const std::exception& e) {
    printf("Caught exception: %s\n", e.what());
    return 1;
}