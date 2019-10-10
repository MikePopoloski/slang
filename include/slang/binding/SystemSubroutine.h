//------------------------------------------------------------------------------
// SystemSubroutine.h
// System-defined subroutine handling.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/ConstantValue.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {

class BindContext;
class EvalContext;
class Expression;
class Type;
struct ExpressionSyntax;

class SystemSubroutine {
public:
    virtual ~SystemSubroutine() = default;

    using Args = span<const Expression* const>;

    std::string name;
    SubroutineKind kind;

    virtual const Expression& bindArgument(int argIndex, const BindContext& context,
                                           const ExpressionSyntax& syntax) const;
    virtual const Type& checkArguments(const BindContext& context, const Args& args,
                                       SourceRange range) const = 0;
    virtual ConstantValue eval(EvalContext& context, const Args& args) const = 0;
    virtual bool verifyConstant(EvalContext& context, const Args& args) const = 0;

protected:
    SystemSubroutine(std::string name, SubroutineKind kind) : name(std::move(name)), kind(kind) {}

    string_view kindStr() const;
    static bool checkArgCount(const BindContext& context, bool isMethod, const Args& args,
                              SourceRange callRange, ptrdiff_t min, ptrdiff_t max);

    static bool checkFormatArgs(const BindContext& context, const Args& args);
};

} // namespace slang