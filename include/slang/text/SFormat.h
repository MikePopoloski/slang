//------------------------------------------------------------------------------
//! @file SFormat.h
//! @brief SystemVerilog string formatting routines
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/Diagnostics.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Function.h"
#include "slang/util/Util.h"

namespace slang {

namespace SFormat {

struct FormatOptions {
    optional<uint32_t> width;
    optional<uint32_t> precision;
    bool leftJustify = false;
    bool zeroPad = false;
};

bool parse(
    string_view formatString, function_ref<void(string_view text)> onText,
    function_ref<void(char specifier, size_t offset, size_t len, const FormatOptions& options)>
        onArg,
    function_ref<void(DiagCode code, size_t offset, size_t len, optional<char> specifier)> onError);

void formatArg(std::string& result, const ConstantValue& arg, char specifier,
               const FormatOptions& options);

} // namespace SFormat

} // namespace slang