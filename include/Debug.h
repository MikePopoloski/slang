//------------------------------------------------------------------------------
// Debug.h
// Debugging utilities and infrastructure.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "ppk_assert/ppk_assert.h"

// Just delegate our assert handling to the 3rd part lib
#define ASSERT PPK_ASSERT

#ifdef DEFAULT_UNREACHABLE
#undef DEFAULT_UNREACHABLE
#endif
#define DEFAULT_UNREACHABLE default: ASSERT(false, "Default case should be unreachable!")