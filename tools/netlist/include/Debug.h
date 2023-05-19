//------------------------------------------------------------------------------
//! @file Debug.h
//! @brief Provide a debug printing macro.
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "Config.h"
#include <iostream>

#ifdef DEBUG
#    define DEBUG_PRINT(x)                                 \
        if (netlist::Config::getInstance().debugEnabled) { \
            std::cerr << x;                                \
        }
#else
#    define DEBUG_PRINT(x)
#endif
