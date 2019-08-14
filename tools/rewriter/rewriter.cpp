//------------------------------------------------------------------------------
// rewriter.cpp
// Simple tool that parses an input file and writes it back out; used
// for verifying the round-trip nature of the parse tree.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------

#include <cstdio>
#if defined(_WIN32)
#    include <fcntl.h>
#    include <io.h>
#endif

#include <filesystem>

#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"

using namespace slang;

int main(int argc, char** argv) try {
    if (argc != 2) {
        fprintf(stderr, "usage: rewriter file\n");
        return 1;
    }

    // Make sure we reproduce newlines correctly on Windows:
#if defined(_WIN32)
    _setmode(_fileno(stdout), _O_BINARY);
#endif

    if (!std::filesystem::exists(argv[1])) {
        fprintf(stderr, "File does not exist: %s\n", argv[1]);
        return 1;
    }

    if (!std::filesystem::is_regular_file(argv[1])) {
        fprintf(stderr, "%s is not a file\n", argv[1]);
        return 1;
    }

    auto tree = SyntaxTree::fromFile(argv[1]);
    printf("%s", SyntaxPrinter::printFile(*tree).c_str());
    return 0;
}
catch (const std::exception& e) {
    printf("internal compiler error (exception): %s\n", e.what());
    return 2;
}