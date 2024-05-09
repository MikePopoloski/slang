//------------------------------------------------------------------------------
// EnumMethods.cpp
// Built-in methods on enums
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "Builtins.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"

namespace slang::ast::builtins {

using namespace syntax;

class EnumFirstLastMethod : public SystemSubroutine {
public:
    EnumFirstLastMethod(const std::string& name, bool first) :
        SystemSubroutine(name, SubroutineKind::Function), first(first) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        return *args[0]->type;
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        if (!noHierarchical(context, *args[0]))
            return nullptr;

        // Expression isn't actually evaluated here; we know the value to return at compile time.
        const EnumType& type = args[0]->type->getCanonicalType().as<EnumType>();

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

private:
    bool first;
};

class EnumNextPrevMethod : public SystemSubroutine {
public:
    EnumNextPrevMethod(const std::string& name, bool next) :
        SystemSubroutine(name, SubroutineKind::Function), next(next) {}

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if (argIndex > 1)
            return SystemSubroutine::bindArgument(argIndex, context, syntax, args);

        return Expression::bindArgument(context.getCompilation().getUnsignedIntType(),
                                        ArgumentDirection::In, {}, syntax, context);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 1))
            return comp.getErrorType();

        return *args[0]->type;
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
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

            // Convert to a signed 33-bit number for delta computation.
            count = countCv.integer();
            count = count.resize(33);
            count.setSigned(true);
        }

        std::optional<size_t> foundIndex;
        SmallVector<const EnumValueSymbol*> values;
        const EnumType& type = args[0]->type->getCanonicalType().as<EnumType>();
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

            values.push_back(&enumerand);
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

private:
    bool next;
};

class EnumNumMethod : public SystemSubroutine {
public:
    EnumNumMethod() : SystemSubroutine("num", SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        if (!noHierarchical(context, *args[0]))
            return nullptr;

        // Expression isn't actually evaluated here; we know the value to return at compile time.
        const EnumType& type = args[0]->type->getCanonicalType().as<EnumType>();
        return SVInt(32, (uint64_t)std::ranges::distance(type.values()), true);
    }
};

class EnumNameMethod : public SimpleSystemSubroutine {
public:
    explicit EnumNameMethod(const Builtins& builtins) :
        SimpleSystemSubroutine("name", SubroutineKind::Function, 0, {}, builtins.stringType, true) {
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        const EnumType& type = args[0]->type->getCanonicalType().as<EnumType>();
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

void Builtins::registerEnumMethods() {
#define REGISTER(kind, name, ...) addSystemMethod(kind, std::make_shared<name##Method>(__VA_ARGS__))
    REGISTER(SymbolKind::EnumType, EnumFirstLast, "first", true);
    REGISTER(SymbolKind::EnumType, EnumFirstLast, "last", false);
    REGISTER(SymbolKind::EnumType, EnumNextPrev, "next", true);
    REGISTER(SymbolKind::EnumType, EnumNextPrev, "prev", false);
    REGISTER(SymbolKind::EnumType, EnumName, *this);
#undef REGISTER

    addSystemMethod(SymbolKind::EnumType, std::make_shared<EnumNumMethod>());
}

} // namespace slang::ast::builtins
