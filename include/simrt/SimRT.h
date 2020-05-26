//------------------------------------------------------------------------------
// SimRT.h
// Simulation runtime exports
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#define EXPORT extern "C"

namespace simrt {

using ExportList = std::vector<std::pair<std::string_view, uintptr_t>>;

/// Gets a list of all exported functions in the runtime. The results are a pair,
/// with the first element being the function's name and the second being
/// a pointer to the function itself.
ExportList getExportedFunctions();

} // namespace simrt