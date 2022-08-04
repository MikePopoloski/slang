//------------------------------------------------------------------------------
// Runtime.h
// Simulation runtime exports
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "slang/util/Function.h"

#define EXPORT extern "C"

namespace slang::runtime {

using ExportList = std::vector<std::pair<std::string_view, uintptr_t>>;

/// Gets a list of all exported functions in the runtime. The results are a pair,
/// with the first element being the function's name and the second being
/// an opaque pointer to the function itself.
ExportList getExportedFunctions();

/// Sets a callback that will be invoked whenever the simulation outputs text.
/// The callback can display that text however it likes. The string_view
/// parameter is only valid for the duration of the callback.
void setOutputHandler(function_ref<void(std::string_view)> handler);

} // namespace slang::runtime
