//------------------------------------------------------------------------------
// Runtime.cpp
// Simulation runtime exports
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/runtime/Runtime.h"

namespace slang::runtime {

void getIOExports(ExportList& results);

ExportList getExportedFunctions() {
    ExportList results;
    getIOExports(results);

    return results;
}

} // namespace slang::runtime
