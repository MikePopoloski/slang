//------------------------------------------------------------------------------
//! @file SystemSubroutine.h
//! @brief System-defined subroutine handling
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/Expression.h"
#include "slang/symbols/AllTypes.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/util/SmallVector.h"
#include "slang/util/Util.h"

namespace slang {

namespace mir {
class Procedure;
}

class SystemSubroutine {
public:
    virtual ~SystemSubroutine() = default;

    using Args = span<const Expression* const>;

    std::string name;
    SubroutineKind kind;

    virtual bool allowEmptyArgument(size_t argIndex) const;
    virtual const Expression& bindArgument(size_t argIndex, const BindContext& context,
                                           const ExpressionSyntax& syntax) const;
    virtual const Type& checkArguments(const BindContext& context, const Args& args,
                                       SourceRange range) const = 0;
    virtual ConstantValue eval(const Scope& scope, EvalContext& context,
                               const Args& args) const = 0;
    virtual bool verifyConstant(EvalContext& context, const Args& args) const = 0;

    virtual void lower(mir::Procedure&, const Args&) const {}

protected:
    SystemSubroutine(const std::string& name, SubroutineKind kind) : name(name), kind(kind) {}

    string_view kindStr() const;
    const Type& badArg(const BindContext& context, const Expression& arg) const;

    static bool checkArgCount(const BindContext& context, bool isMethod, const Args& args,
                              SourceRange callRange, size_t min, size_t max);

    static bool checkFormatArgs(const BindContext& context, const Args& args);

    static bool checkFormatValues(const BindContext& context, const Args& args);

    static void lowerFormatArgs(mir::Procedure& proc, const Args& args, LiteralBase defaultIntFmt);

    static BindContext makeNonConst(const BindContext& context);
};

/// An implementation of the SystemSubroutine interface that has
/// basic argument types and a well-defined return type.
class SimpleSystemSubroutine : public SystemSubroutine {
public:
    const Expression& bindArgument(size_t argIndex, const BindContext& context,
                                   const ExpressionSyntax& syntax) const final;
    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final;
    bool verifyConstant(EvalContext&, const Args&) const override { return true; }

protected:
    SimpleSystemSubroutine(const std::string& name, SubroutineKind kind, size_t requiredArgs,
                           const std::vector<const Type*>& argTypes, const Type& returnType,
                           bool isMethod, bool allowNonConst = false) :
        SystemSubroutine(name, kind),
        argTypes(argTypes), returnType(&returnType), requiredArgs(requiredArgs), isMethod(isMethod),
        allowNonConst(allowNonConst) {
        ASSERT(requiredArgs <= argTypes.size());
    }

private:
    std::vector<const Type*> argTypes;
    const Type* returnType;
    size_t requiredArgs;
    bool isMethod;
    bool allowNonConst;
};

} // namespace slang