//------------------------------------------------------------------------------
// rewriter.cpp
// Simple tool that parses an input file and writes it back out; used
// for verifying the round-trip nature of the parse tree.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------

#include <cstdio>
#if defined(_WIN32)
  #include <fcntl.h>
  #include <io.h>
#endif

#include "lexing/SyntaxPrinter.h"
#include "parsing/SyntaxTree.h"

using namespace slang;

int main(int argc, char** argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: rewriter file");
        return 1;
    }

    // Make sure we reproduce newlines correctly on Windows:
#if defined(_WIN32)
    _setmode(_fileno(stdout), _O_BINARY);
#endif

    auto tree = SyntaxTree::fromFile(argv[1]);

    std::string output = SyntaxPrinter()
        .setIncludeDirectives(true)
        .setIncludeSkipped(true)
        .setIncludeTrivia(true)
        .excludePreprocessed(tree->sourceManager())
        .print(tree->root())
        .str();

    printf("%s", output.c_str());
    return 0;
}