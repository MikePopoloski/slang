//------------------------------------------------------------------------------
// print.cpp
// Runtime print output routines
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "simrt/SimRT.h"
#include <cstdio>

EXPORT void printChar(int8_t c) {
    printf("'%c'\n", c);
}

namespace simrt {

void getIOExports(ExportList& results) {
#define ADD(name) results.emplace_back(#name, reinterpret_cast<uintptr_t>(&(name)));

    ADD(printChar);

#undef ADD
}

} // namespace simrt