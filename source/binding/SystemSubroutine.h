//------------------------------------------------------------------------------
// SystemSubroutine.h
// System-defined subroutine handling.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "binding/ConstantValue.h"
#include "util/SmallVector.h"
#include "util/Util.h"

namespace slang {

class Compilation;
class EvalContext;
class Expression;
class Type;

class SystemSubroutine {
public:
    virtual ~SystemSubroutine() = default;

    using Args = span<const Expression* const>;

    std::string name;

    virtual const Type& checkArguments(Compilation& compilation, const Args& args) const = 0;
    virtual ConstantValue eval(EvalContext& context, const Args& args) const = 0;

protected:
    explicit SystemSubroutine(std::string name) : name(std::move(name)) {}
};

}