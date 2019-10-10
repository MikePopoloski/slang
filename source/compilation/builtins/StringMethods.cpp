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

class StringLenMethod : public SimpleSystemSubroutine {
public:
    StringLenMethod(Compilation& comp) :
        SimpleSystemSubroutine("len", SubroutineKind::Function, 0, {}, comp.getIntType(), true) {}

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        return SVInt(32, val.str().length(), true);
    }
};

class StringUpperLowerMethod : public SimpleSystemSubroutine {
public:
    StringUpperLowerMethod(Compilation& comp, const std::string& name, bool upper) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, 0, {}, comp.getStringType(), true),
        upper(upper) {}

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

private:
    bool upper;
};

void registerStringMethods(Compilation& c) {
#define REGISTER(kind, name, ...) \
    c.addSystemMethod(kind, std::make_unique<name##Method>(__VA_ARGS__))
    REGISTER(SymbolKind::StringType, StringLen, c);
    REGISTER(SymbolKind::StringType, StringUpperLower, c, "toupper", true);
    REGISTER(SymbolKind::StringType, StringUpperLower, c, "tolower", false);

#undef REGISTER
}

} // namespace slang::Builtins