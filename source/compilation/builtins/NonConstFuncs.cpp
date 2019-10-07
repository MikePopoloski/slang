//------------------------------------------------------------------------------
// NonConstFuncs.cpp
// Built-in non-constant system functions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"

namespace slang::Builtins {

class NonConstantFunction : public SystemSubroutine {
public:
    NonConstantFunction(const std::string& name, const Type& returnType) :
        SystemSubroutine(name, SubroutineKind::Function), returnType(returnType) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 0, 0))
            return comp.getErrorType();

        return returnType;
    }

    ConstantValue eval(EvalContext&, const Args&) const final { return nullptr; }
    bool verifyConstant(EvalContext&, const Args&) const final { return false; }

private:
    const Type& returnType;
};

void registerNonConstFuncs(Compilation& c) {
#define REGISTER(name, returnType) \
    c.addSystemSubroutine(std::make_unique<NonConstantFunction>(name, returnType))

    auto& uintType = c.getType(32, IntegralFlags::Unsigned);
    REGISTER("$time", c.getTimeType());
    REGISTER("$stime", uintType);
    REGISTER("$realtime", c.getRealTimeType());

    // TODO: optional argument to random functions
    REGISTER("$random", c.getIntType());
    REGISTER("$urandom", uintType);

#undef REGISTER
}

} // namespace slang::Builtins