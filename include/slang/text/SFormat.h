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
        enum { Integral, Raw, Float, Net, Pattern, Character, String } kind;
        char spec;
    };

    span<const Arg> specifiers() const { return specs; }

private:
    SmallVectorSized<Arg, 8> specs;
    Diagnostics diags;
};

} // namespace slang