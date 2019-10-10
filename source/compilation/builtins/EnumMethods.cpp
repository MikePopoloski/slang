//------------------------------------------------------------------------------
// EnumMethods.cpp
// Built-in methods on enums.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"

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

class EnumNextPrevMethod : public SystemSubroutine {
public:
    EnumNextPrevMethod(const std::string& name, bool next) :
        SystemSubroutine(name, SubroutineKind::Function), next(next) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 1))
            return comp.getErrorType();

        if (args.size() == 2) {
            if (!args[1]->type->isIntegral()) {
                context.addDiag(diag::BadSystemSubroutineArg, args[1]->sourceRange)
                    << *args[1]->type << kindStr();
                return comp.getErrorType();
            }
        }

        return *args.at(0)->type;
    }

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        // Count defaults to 1, but can optionally be passed in.
        SVInt one(33, 1, true);
        SVInt count = one;
        if (args.size() == 2) {
            auto countCv = args[1]->eval(context);
            if (!countCv)
                return nullptr;

            count = countCv.integer();
            count.flattenUnknowns();

            // Truncate any of the high bits.
            count.setSigned(false);
            count = count.resize(32);

            // Convert back to a signed 33-bit number for delta computation.
            count = count.resize(33);
            count.setSigned(true);
        }

        optional<size_t> foundIndex;
        SmallVectorSized<const EnumValueSymbol*, 8> values;
        const EnumType& type = args.at(0)->type->getCanonicalType().as<EnumType>();
        auto& targetInt = val.integer();

        // Get all values into an array for easier handling. Along the way,
        // try to find the current value among the enum members.
        size_t current = 0;
        for (auto& enumerand : type.values()) {
            auto& cv = enumerand.getValue();
            if (!cv)
                return nullptr;

            if (cv.integer() == targetInt)
                foundIndex = current;

            values.append(&enumerand);
            current++;
        }

        if (values.empty())
            return nullptr;

        // If the current value is not in the set of enumerands, the spec
        // says we should return the default value.
        if (!foundIndex.has_value())
            return type.getDefaultValue();

        if (!next)
            count = -count;

        // Handle wraparound for both zero and the size of the array.
        SVInt size(33, values.size(), true);
        SVInt offset = SVInt(33, *foundIndex, true) + count;
        offset += (one - offset / size) * size;

        count = offset % SVInt(33, values.size(), true);
        uint32_t i = count.as<uint32_t>().value();
        return values[i]->getValue();
    }

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }

private:
    bool next;
};

class EnumNumMethod : public SimpleSystemSubroutine {
public:
    EnumNumMethod(Compilation& comp) :
        SimpleSystemSubroutine("num", SubroutineKind::Function, 0, {}, comp.getIntType(), true) {}

    ConstantValue eval(EvalContext&, const Args& args) const final {
        // Expression isn't actually evaluated here; we know the value to return at compile time.
        const EnumType& type = args.at(0)->type->getCanonicalType().as<EnumType>();
        return SVInt(32, (uint64_t)type.values().size(), true);
    }
};

class EnumNameMethod : public SimpleSystemSubroutine {
public:
    EnumNameMethod(Compilation& comp) :
        SimpleSystemSubroutine("name", SubroutineKind::Function, 0, {}, comp.getStringType(),
                               true) {}

    ConstantValue eval(EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        const EnumType& type = args.at(0)->type->getCanonicalType().as<EnumType>();
        auto& targetInt = val.integer();

        for (auto& enumerand : type.values()) {
            auto& cv = enumerand.getValue();
            if (!cv)
                return nullptr;

            if (cv.integer() == targetInt)
                return std::string(enumerand.name);
        }

        return ""s;
    }
};

void registerEnumMethods(Compilation& c) {
#define REGISTER(kind, name, ...) \
    c.addSystemMethod(kind, std::make_unique<name##Method>(__VA_ARGS__))
    REGISTER(SymbolKind::EnumType, EnumFirstLast, "first", true);
    REGISTER(SymbolKind::EnumType, EnumFirstLast, "last", false);
    REGISTER(SymbolKind::EnumType, EnumNextPrev, "next", true);
    REGISTER(SymbolKind::EnumType, EnumNextPrev, "prev", false);
    REGISTER(SymbolKind::EnumType, EnumNum, c);
    REGISTER(SymbolKind::EnumType, EnumName, c);
#undef REGISTER
}

} // namespace slang::Builtins