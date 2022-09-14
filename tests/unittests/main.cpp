// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

#include <catch2/catch_session.hpp>

#include "slang/diagnostics/Diagnostics.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/SourceManager.h"
#include "slang/util/BumpAllocator.h"

#if defined(_MSC_VER)
#    include <Windows.h>
#endif

namespace slang {

BumpAllocator alloc;
Diagnostics diagnostics;

} // namespace slang

int main(int argc, char* argv[]) {
#if defined(_MSC_VER)
    SetConsoleOutputCP(CP_UTF8);
    setvbuf(stdout, nullptr, _IOFBF, 1000);
#endif

    slang::SyntaxTree::getDefaultSourceManager().setDisableProximatePaths(true);

    Catch::Session session;
    session.configData().defaultColourMode = Catch::ColourMode::ANSI;
    return session.run(argc, argv);
}
