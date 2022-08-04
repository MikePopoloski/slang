//------------------------------------------------------------------------------
// SimIO.cpp
// Simulation IO routines
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include <fmt/format.h>

#include "slang/runtime/Runtime.h"
#include "slang/text/SFormat.h"
#include "slang/util/OS.h"

using namespace slang;

// The global output buffer, printed to by exported I/O routines.
// Whenever flush() is called the outputHandler will be invoked with
// the current contents of the buffer.
fmt::memory_buffer outputBuffer;

function_ref<void(std::string_view)> outputHandler = [](std::string_view str) {
    OS::print("{}", str);
};

EXPORT void flush(bool newline) {
    if (newline)
        outputBuffer.push_back('\n');

    outputHandler(std::string_view(outputBuffer.data(), outputBuffer.size()));
    outputBuffer.clear();
}

EXPORT void printStr(const char* str, size_t len) {
    outputBuffer.append(str, str + len);
}

EXPORT void printInt(const SVInt* value, LiteralBase base, uint32_t width, bool hasWidth) {
    SFormat::FormatOptions options;
    if (hasWidth)
        options.width = width;

    static std::string str;
    SFormat::formatInt(str, *value, base, options);

    outputBuffer.append(str.data(), str.data() + str.size());
    str.clear();
}

namespace slang::runtime {

void setOutputHandler(function_ref<void(std::string_view)> handler) {
    outputHandler = handler;
}

void getIOExports(ExportList& results) {
#define ADD(name) results.emplace_back(#name, reinterpret_cast<uintptr_t>(&(name)));

    ADD(flush);
    ADD(printStr);
    ADD(printInt);

#undef ADD
}

} // namespace slang::runtime
