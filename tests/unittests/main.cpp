// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include <catch2/catch_session.hpp>

#include "slang/diagnostics/Diagnostics.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/OS.h"

namespace slang {

BumpAllocator alloc;
Diagnostics diagnostics;

} // namespace slang

int main(int argc, char* argv[]) {
    slang::OS::setupConsole();

    slang::syntax::SyntaxTree::getDefaultSourceManager().setDisableProximatePaths(true);

    Catch::Session session;
    session.configData().defaultColourMode = Catch::ColourMode::ANSI;
    return session.run(argc, argv);
}
