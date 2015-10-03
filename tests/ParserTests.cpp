#include "catch.hpp"
#include "slang.h"

using namespace slang;

namespace {

BumpAllocator alloc;
Diagnostics diagnostics;
SourceTracker sourceTracker;
Preprocessor preprocessor(sourceTracker, alloc, diagnostics);

TEST_CASE("Test parser", "[parser]") {
    diagnostics.clear();
    Lexer lexer(FileID(), "", preprocessor);

    Parser parser(lexer);
}

}