//------------------------------------------------------------------------------
// BuiltInSubroutines.cpp
// Built-in system subroutine handlers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "BuiltInSubroutines.h"

#include "slang/compilation/Compilation.h"

namespace slang::Builtins {

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
    return SVInt(32, range.lower(), true);
}

ConstantValue HighSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(32, range.upper(), true);
}

ConstantValue LeftSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(32, range.left, true);
}

ConstantValue RightSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(32, range.right, true);
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
    return SVInt(32, range.isLittleEndian() ? 1 : -1, true);
}

} // namespace slang::Builtins