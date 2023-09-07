//------------------------------------------------------------------------------
// rewriter.cpp
// Simple tool that parses an input file and writes it back out; used
// for verifying the round-trip nature of the parse tree.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------

#include <cstdio>
#if defined(_WIN32)
#    include <fcntl.h>
#    include <io.h>
#endif

#include <fmt/format.h>

#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/util/OS.h"

using namespace slang;
using namespace slang::syntax;

int main(int argc, char** argv) {
    OS::setupConsole();

    SLANG_TRY {
        if (argc != 2) {
            fmt::print(stderr, "usage: rewriter file\n");
            return 1;
        }

        auto tree = SyntaxTree::fromFile(argv[1]);
        if (!tree) {
            fmt::print(stderr, "error: '{}': {}\n", argv[1], tree.error().first.message());
            return 1;
        }

        // Make sure we reproduce newlines correctly on Windows:
#if defined(_WIN32)
        _setmode(_fileno(stdout), _O_BINARY);
#endif

        printf("%s", SyntaxPrinter::printFile(*tree.value()).c_str());
        return 0;
    }
    SLANG_CATCH(const std::exception& e) {
#if __cpp_exceptions
        printf("internal compiler error (exception): %s\n", e.what());
#endif
        return 2;
    }
}
