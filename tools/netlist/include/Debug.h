#pragma once

#include <iostream>

#include "Config.h"

#ifdef DEBUG
#define DEBUG_PRINT(x) if (netlist::Config::getInstance().debugEnabled) { std::cerr << x; }
#else
#define DEBUG_PRINT(x)
#endif
