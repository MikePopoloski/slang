//------------------------------------------------------------------------------
// EnumMethods.cpp
// Built-in methods on enums.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"

namespace slang::Builtins {

class EnumFirstLastMethod : public SystemSubroutine {
public:
    EnumFirstLastMethod(const std::string& name, bool first) :
        SystemSubroutine(name, SubroutineKind::Function), first(first) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        return *args.at(0)->type;
    }

    ConstantValue eval(EvalContext&, const Args& args) const final {
        // Expression isn't actually evaluated here; we know the value to return at compile time.
        const EnumType& type = args.at(0)->type->getCanonicalType().as<EnumType>();

        auto range = type.values();
        if (range.begin() == range.end())
            return nullptr;

        const EnumValueSymbol* value;
        if (first) {
            value = &*range.begin();
        }
        else {
            for (auto it = range.begin();;) {
                auto prev = it++;
                if (it == range.end()) {
                    value = &*prev;
                    break;
                }
            }
        }

        return value->getValue();
    }

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }

private:
    bool first;
};

class EnumNumMethod : public SystemSubroutine {
public:
    EnumNumMethod() : SystemSubroutine("num", SubroutineKind::Function) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        return comp.getIntegerType();
    }

    ConstantValue eval(EvalContext&, const Args& args) const final {
        // Expression isn't actually evaluated here; we know the value to return at compile time.
        const EnumType& type = args.at(0)->type->getCanonicalType().as<EnumType>();
        return SVInt(32, (uint64_t)type.values().size(), true);
    }

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
};

void registerEnumMethods(Compilation& c) {
#define REGISTER(kind, name, ...) \
    c.addSystemMethod(kind, std::make_unique<name##Method>(__VA_ARGS__))
    REGISTER(SymbolKind::EnumType, EnumFirstLast, "first", true);
    REGISTER(SymbolKind::EnumType, EnumFirstLast, "last", false);
    REGISTER(SymbolKind::EnumType, EnumNum, );
#undef REGISTER
}

} // namespace slang::Builtins