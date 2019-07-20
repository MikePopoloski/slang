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

class SFormat {
public:
    SFormat(string_view formatString, SourceLocation loc);

    bool valid() const { return diags.empty(); }
    const Diagnostics& getDiagnostics() const { return diags; }

    struct Arg {
        enum Type { Integral, Raw, Float, Net, Pattern, Character, String, None } type;
        char spec;
    };

    span<const Arg> specifiers() const { return specs; }

    using TypedValue = std::tuple<ConstantValue, const Type*, SourceRange>;

    static optional<std::string> format(string_view formatString, SourceLocation loc,
                                        span<const TypedValue> args, Diagnostics& diags);

    static bool isArgTypeValid(Arg::Type required, const Type& type);

private:
    SmallVectorSized<Arg, 8> specs;
    Diagnostics diags;
};

} // namespace slang