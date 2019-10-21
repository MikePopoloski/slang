//------------------------------------------------------------------------------
// ConversionFuncs.cpp
// Built-in conversion system functions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang::Builtins {

class SignedConversionFunction : public SystemSubroutine {
public:
    SignedConversionFunction(const std::string& name, bool toSigned) :
        SystemSubroutine(name, SubroutineKind::Function), toSigned(toSigned) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, 1, 1))
            return comp.getErrorType();

        auto& type = *args[0]->type;
        if (!type.isIntegral()) {
            context.addDiag(diag::BadSystemSubroutineArg, args[0]->sourceRange)
                << type << kindStr();
            return comp.getErrorType();
        }

        auto flags = type.getIntegralFlags() & ~IntegralFlags::Signed;
        if (toSigned)
            flags |= IntegralFlags::Signed;

        return comp.getType(type.getBitWidth(), flags);
    }

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        const Type& to = *args[0]->type;
        return val.convertToInt(to.getBitWidth(), toSigned, to.isFourState());
    }

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }

private:
    bool toSigned;
};

void registerConversionFuncs(Compilation& c) {
#define REGISTER(name, ...) c.addSystemSubroutine(std::make_unique<name##Function>(__VA_ARGS__))
    REGISTER(SignedConversion, "$signed", true);
    REGISTER(SignedConversion, "$unsigned", false);
#undef REGISTER
}

} // namespace slang::Builtins