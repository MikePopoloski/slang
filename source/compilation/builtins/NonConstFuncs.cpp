//------------------------------------------------------------------------------
// NonConstFuncs.cpp
// Built-in non-constant system functions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"

namespace slang::Builtins {

class NonConstantFunction : public SimpleSystemSubroutine {
public:
    NonConstantFunction(const std::string& name, const Type& returnType, size_t requiredArgs = 0,
                        const std::vector<const Type*>& argTypes = {}) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, requiredArgs, argTypes, returnType,
                               false) {}

    ConstantValue eval(EvalContext&, const Args&) const final { return nullptr; }
    bool verifyConstant(EvalContext&, const Args&) const final { return false; }
};

void registerNonConstFuncs(Compilation& c) {
#define REGISTER(...) c.addSystemSubroutine(std::make_unique<NonConstantFunction>(__VA_ARGS__))

    auto& intType = c.getIntType();
    std::vector<const Type*> intArg = { &intType };

    REGISTER("$time", c.getTimeType());
    REGISTER("$stime", c.getUnsignedIntType());
    REGISTER("$realtime", c.getRealTimeType());
    REGISTER("$random", intType, 0, intArg);
    REGISTER("$urandom", c.getUnsignedIntType(), 0, intArg);

    REGISTER("$fopen", intType, 1, std::vector{ &c.getStringType(), &c.getStringType() });
    REGISTER("$fclose", c.getVoidType(), 1, intArg);
    REGISTER("$fgetc", intType, 1, intArg);
    REGISTER("$ungetc", intType, 2, std::vector{ &intType, &intType });
    REGISTER("$ftell", intType, 1, intArg);
    REGISTER("$fseek", intType, 3, std::vector{ &intType, &intType, &intType });
    REGISTER("$rewind", intType, 1, intArg);
    REGISTER("$fflush", c.getVoidType(), 0, intArg);
    REGISTER("$feof", intType, 1, intArg);

    REGISTER("$test$plusargs", intType, 1, std::vector{ &c.getStringType() });

#undef REGISTER
}

} // namespace slang::Builtins