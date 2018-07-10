//------------------------------------------------------------------------------
// BuiltInSubroutines.cpp
// Built-in system subroutine handlers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "BuiltInSubroutines.h"

#include "Compilation.h"

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
    return SVInt(clog2(v.integer()));
}

ConstantValue BitsSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    return SVInt(argType.bitWidth);
}

ConstantValue LowSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(range.lower());
}

ConstantValue HighSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(range.upper());
}

ConstantValue LeftSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(range.left);
}

ConstantValue RightSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(range.right);
}

ConstantValue SizeSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    // TODO: bitwidth is not quite right here
    const auto& argType = args[0]->type->as<IntegralType>();
    return SVInt(argType.bitWidth);
}

ConstantValue IncrementSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: other types?
    const auto& argType = args[0]->type->as<IntegralType>();
    ConstantRange range = argType.getBitVectorRange();
    return SVInt(range.isLittleEndian() ? 1 : -1);
}

}