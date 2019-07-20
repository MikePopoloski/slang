//------------------------------------------------------------------------------
// SFormat.h
// SystemVerilog string formatting routines.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/Diagnostics.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Util.h"

namespace slang {

namespace SFormat {

struct Arg {
    enum Type { Integral, Raw, Float, Net, Pattern, Character, String, None } type;
    char spec;
};

using TypedValue = std::tuple<ConstantValue, const Type*, SourceRange>;

bool parseArgs(string_view formatString, SourceLocation loc, SmallVector<Arg>& args,
               Diagnostics& diags);

optional<std::string> format(string_view formatString, SourceLocation loc,
                             span<const TypedValue> args, Diagnostics& diags);

bool isArgTypeValid(Arg::Type required, const Type& type);

} // namespace SFormat

} // namespace slang