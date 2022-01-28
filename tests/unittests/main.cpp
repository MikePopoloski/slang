#define CATCH_CONFIG_RUNNER
#include <catch2/catch.hpp>

// This file contains the Catch unit testing framework implementation
// as well as the main() function, with command line arg parsing.
//
// See documentation at: https://github.com/philsquared/Catch
//
// Don't put tests in this file; we want to avoid recompiling the
// Catch impl whenever we modify a test.

#include "slang/diagnostics/Diagnostics.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"
#include "slang/util/BumpAllocator.h"

namespace slang {

BumpAllocator alloc;
Diagnostics diagnostics;

} // namespace slang

int main(int argc, char* argv[]) {
    slang::SyntaxTree::getDefaultSourceManager().setDisableProximatePaths(true);
    return Catch::Session().run(argc, argv);
}
