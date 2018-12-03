//------------------------------------------------------------------------------
// BuiltInSubroutines.cpp
// Built-in system subroutine handlers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "BuiltInSubroutines.h"

#include "slang/compilation/Compilation.h"

namespace slang::Builtins {

// TODO: check all of these for whether return type should be int or integer

const Type& IntegerMathFunction::checkArguments(Compilation& compilation, const Args&) const {
    // TODO: error checking
    return compilation.getIntegerType();
}

const Type& DataQueryFunction::checkArguments(Compilation& compilation, const Args&) const {
    // TODO: error checking
    return compilation.getIntegerType();
}

const Type& ArrayQueryFunction::checkArguments(Compilation& compilation, const Args&) const {
    // TODO: error checking
    return compilation.getIntegerType();
}

ConstantValue Clog2Subroutine::eval(EvalContext& context, const Args& args) const {
    ConstantValue v = args[0]->eval(context);
    if (!v)
        return nullptr;

    // TODO: other types?
    return SVInt(32, clog2(v.integer()), true);
}

ConstantValue BitsSubroutine::eval(EvalContext&, const Args& args) const {
    return SVInt(32, args[0]->type->getBitWidth(), true);
}

ConstantValue LowSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(32, (uint64_t)range.lower(), true);
}

ConstantValue HighSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(32, (uint64_t)range.upper(), true);
}

ConstantValue LeftSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(32, (uint64_t)range.left, true);
}

ConstantValue RightSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(32, (uint64_t)range.right, true);
}

ConstantValue SizeSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    // TODO: bitwidth is not quite right here
    const auto& argType = args[0]->type->as<IntegralType>();
    return SVInt(32, argType.bitWidth, true);
}

ConstantValue IncrementSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(32, (uint64_t)(range.isLittleEndian() ? 1 : -1), true);
}

EnumFirstLastMethod::EnumFirstLastMethod(std::string name, bool first) :
    SystemSubroutine(std::move(name)), first(first) {
}

const Type& EnumFirstLastMethod::checkArguments(Compilation&, const Args& args) const {
    // TODO: check too many args
    return *args.at(0)->type;
}

ConstantValue EnumFirstLastMethod::eval(EvalContext&, const Args& args) const {
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

const Type& EnumNumMethod::checkArguments(Compilation& compilation, const Args&) const {
    // TODO: check too many args
    return compilation.getIntegerType();
}

ConstantValue EnumNumMethod::eval(EvalContext&, const Args& args) const {
    // Expression isn't actually evaluated here; we know the value to return at compile time.
    const EnumType& type = args.at(0)->type->getCanonicalType().as<EnumType>();
    return SVInt(32, (uint64_t)type.values().size(), true);
}

} // namespace slang::Builtins