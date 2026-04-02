//------------------------------------------------------------------------------
// CSTMemoryStats.h
// Memory usage statistics for the CST (Concrete Syntax Tree).
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <string>

#include "slang/util/Util.h"

namespace slang::driver {
class Driver;
}

/// Prints memory usage statistics for all parsed CST syntax trees held by @a driver.
/// May be called as soon as parsing is complete, even when elaboration is skipped.
/// Output is written to @a fileName; use "-" for stdout.
SLANG_EXPORT void printCSTMemoryStats(slang::driver::Driver& driver, const std::string& fileName);
