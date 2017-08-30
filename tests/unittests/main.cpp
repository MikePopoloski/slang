#define CATCH_CONFIG_MAIN
#define DO_NOT_USE_WMAIN
#include "Catch/catch.hpp"

// This file contains the Catch unit testing framework implementation
// as well as the main() function, with command line arg parsing.
//
// See documentation at: https://github.com/philsquared/Catch
//
// Don't put tests in this file; we want to avoid recompiling the
// Catch impl whenever we modify a test.

#include "util/BumpAllocator.h"
#include "diagnostics/Diagnostics.h"

slang::BumpAllocator alloc;
slang::Diagnostics diagnostics;