//------------------------------------------------------------------------------
// NonConstFuncs.cpp
// Built-in non-constant system functions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"

namespace slang::Builtins {

class NonConstantFunction : public SimpleSystemSubroutine {
public:
    NonConstantFunction(const std::string& name, const Type& returnType, int requiredArgs = 0,
                        const std::vector<const Type*>& argTypes = {}) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, requiredArgs, argTypes, returnType,
                               false) {}

    ConstantValue eval(EvalContext&, const Args&) const final { return nullptr; }
    bool verifyConstant(EvalContext&, const Args&) const final { return false; }
};

void registerNonConstFuncs(Compilation& c) {
#define REGISTER(...) \
    c.addSystemSubroutine(std::make_unique<NonConstantFunction>(__VA_ARGS__))

    std::vector<const Type*> intArg = { &c.getIntType() };

    REGISTER("$time", c.getTimeType());
    REGISTER("$stime", c.getUnsignedIntType());
    REGISTER("$realtime", c.getRealTimeType());
    REGISTER("$random", c.getIntType(), 0, intArg);
    REGISTER("$urandom", c.getUnsignedIntType(), 0, intArg);

#undef REGISTER
}

} // namespace slang::Builtins