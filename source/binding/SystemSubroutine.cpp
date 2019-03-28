//------------------------------------------------------------------------------
// SystemSubroutine.cpp
// System-defined subroutine handling.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"

#include "slang/binding/BindContext.h"
#include "slang/binding/Expressions.h"

namespace slang {

string_view SystemSubroutine::kindStr() const {
    // TODO: also check for tasks
    return "function"sv;
}

bool SystemSubroutine::checkArgCount(const BindContext& context, bool isMethod, const Args& args,
                                     size_t expected) {
    size_t provided = args.size();
    if (isMethod) {
        ASSERT(provided);
        provided--;
    }

    if (provided != expected) {
        Diagnostic* diag;
        if (provided > expected)
            diag = &context.addDiag(DiagCode::TooManyArguments, args[expected]->sourceRange);
        else
            diag = &context.addDiag(DiagCode::TooFewArguments, args[expected]->sourceRange);
        (*diag) << expected << provided;

        return false;
    }

    for (auto arg : args) {
        if (arg->bad())
            return false;
    }

    return true;
}

} // namespace slang