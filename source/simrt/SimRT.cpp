//------------------------------------------------------------------------------
// SimRT.cpp
// Simulation runtime exports
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "simrt/SimRT.h"

namespace simrt {

void getIOExports(ExportList& results);

ExportList getExportedFunctions() {
    ExportList results;
    getIOExports(results);
    
    return results;
}

} // namespace simrt