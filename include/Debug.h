//------------------------------------------------------------------------------
// Debug.h
// Debugging utilities and infrastructure.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "pempek_assert/pempek_assert.h"

// Just delegate our assert handling to the 3rd part lib
#define ASSERT PPK_ASSERT

#define DEFAULT_UNREACHABLE default: ASSERT(false, "Default case should be unreachable!")