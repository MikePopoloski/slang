//------------------------------------------------------------------------------
//! @file FormatHelpers.h
//! @brief Helpers for implementing the string formatting system functions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/numeric/SVInt.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Util.h"

namespace slang {

class BindContext;
class Expression;
class EvalContext;
class Scope;

namespace mir {
class Procedure;
}

class FmtHelpers {
public:
    static bool checkDisplayArgs(const BindContext& context,
                                 const span<const Expression* const>& args);

    static bool checkSFormatArgs(const BindContext& context,
                                 const span<const Expression* const>& args);

    static optional<std::string> formatArgs(string_view formatString, SourceLocation loc,
                                            const Scope& scope, EvalContext& context,
                                            const span<const Expression* const>& args,
                                            bool isStringLiteral);

    static optional<std::string> formatDisplay(const Scope& scope, EvalContext& context,
                                               const span<const Expression* const>& args);

    static void lowerFormatArgs(mir::Procedure& proc, const span<const Expression* const>& args,
                                LiteralBase defaultIntFmt, bool newline);

    static bool checkFinishNum(const BindContext& context, const Expression& arg);

private:
    FmtHelpers() = default;
};

} // namespace slang
