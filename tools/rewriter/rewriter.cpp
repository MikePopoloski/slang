//------------------------------------------------------------------------------
// rewriter.cpp
// Simple tool that parses an input file and writes it back out; used
// for verifying the round-trip nature of the parse tree.
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------

#include <cstdio>

#include "parsing/SyntaxTree.h"

using namespace slang;

int main(int argc, char** argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: rewriter file");
        return 1;
    }

    SmallVectorSized<char, 8> buffer;
    auto tree = SyntaxTree::fromFile(argv[1]);
    tree->root().writeTo(buffer, SyntaxToStringFlags::IncludeTrivia | SyntaxToStringFlags::IncludeDirectives |
                         SyntaxToStringFlags::IncludeSkipped);

    buffer.append('\0');
    puts(buffer.data());

    return 0;
}