//------------------------------------------------------------------------------
// SimIO.cpp
// Simulation IO routines
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include <cstdio>

#include "slang/runtime/Runtime.h"
#include "slang/text/SFormat.h"

using namespace slang;

EXPORT void printChar(int8_t c) {
    printf("'%c'\n", c);
}

EXPORT void printInt(const SVInt* value, LiteralBase base, uint32_t width, bool hasWidth) {
    SFormat::FormatOptions options;
    if (hasWidth)
        options.width = width;

    std::string str;
    SFormat::formatInt(str, *value, base, options);
    printf("%s", str.c_str());
}

namespace slang::runtime {

void getIOExports(ExportList& results) {
#define ADD(name) results.emplace_back(#name, reinterpret_cast<uintptr_t>(&(name)));

    ADD(printChar);
    ADD(printInt);

#undef ADD
}

} // namespace slang::runtime