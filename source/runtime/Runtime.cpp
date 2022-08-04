//------------------------------------------------------------------------------
// Runtime.cpp
// Simulation runtime exports
//
// File is under the MIT license; see LICENSE for details
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
