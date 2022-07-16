#include <catch2/catch_session.hpp>

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
