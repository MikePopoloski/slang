//------------------------------------------------------------------------------
// StringMethods.cpp
// Built-in methods on strings.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang::Builtins {

class StringLenMethod : public SystemSubroutine {
public:
    StringLenMethod() : SystemSubroutine("len", SubroutineKind::Function) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        return SVInt(32, val.str().length(), true);
    }

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

class StringUpperLowerMethod : public SystemSubroutine {
public:
    StringUpperLowerMethod(const std::string& name, bool upper) :
        SystemSubroutine(name, SubroutineKind::Function), upper(upper) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        return comp.getStringType();
    }

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        std::string& str = val.str();
        if (upper) {
            std::transform(str.begin(), str.end(), str.begin(),
                           [](unsigned char c) { return std::toupper(c); });
        }
        else {
            std::transform(str.begin(), str.end(), str.begin(),
                           [](unsigned char c) { return std::tolower(c); });
        }
        return val;
    }

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }

private:
    bool upper;
};

void registerStringMethods(Compilation& c) {
#define REGISTER(kind, name, ...) \
    c.addSystemMethod(kind, std::make_unique<name##Method>(__VA_ARGS__))
    REGISTER(SymbolKind::StringType, StringLen, );
    REGISTER(SymbolKind::StringType, StringUpperLower, "toupper", true);
    REGISTER(SymbolKind::StringType, StringUpperLower, "tolower", false);

#undef REGISTER
}

} // namespace slang::Builtins