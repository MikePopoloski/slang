//------------------------------------------------------------------------------
// BuiltInSubroutines.cpp
// Built-in system subroutine handlers.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "BuiltInSubroutines.h"

#include "slang/compilation/Compilation.h"

namespace slang::Builtins {

const Type& IntegerMathFunction::checkArguments(const BindContext& context,
                                                const Args& args) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, false, args, 1))
        return comp.getErrorType();

    if (!args[0]->type->isIntegral()) {
        context.addDiag(DiagCode::BadSystemSubroutineArg, args[0]->sourceRange)
            << *args[0]->type << kindStr();
        return comp.getErrorType();
    }

    return comp.getIntegerType();
}

const Type& DataQueryFunction::checkArguments(const BindContext& context, const Args& args) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, false, args, 1))
        return comp.getErrorType();

    if (!args[0]->type->isBitstreamType()) {
        context.addDiag(DiagCode::BadSystemSubroutineArg, args[0]->sourceRange)
            << *args[0]->type << kindStr();
        return comp.getErrorType();
    }

    // TODO: not allowed on some dynamic types

    return comp.getIntegerType();
}

const Type& ArrayQueryFunction::checkArguments(const BindContext& context, const Args& args) const {
    // TODO: support optional second argument
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, false, args, 1))
        return comp.getErrorType();

    auto& type = *args[0]->type;
    if (!type.isIntegral() && !type.isUnpackedArray()) {
        context.addDiag(DiagCode::BadSystemSubroutineArg, args[0]->sourceRange)
            << type << kindStr();
        return comp.getErrorType();
    }

    // TODO: not allowed on some dynamic types

    return comp.getIntegerType();
}

ConstantValue Clog2Subroutine::eval(EvalContext& context, const Args& args) const {
    ConstantValue v = args[0]->eval(context);
    if (!v)
        return nullptr;

    return SVInt(32, clog2(v.integer()), true);
}

ConstantValue BitsSubroutine::eval(EvalContext&, const Args& args) const {
    // TODO: support for unpacked sizes
    return SVInt(32, args[0]->type->getBitWidth(), true);
}

ConstantValue LowSubroutine::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)range.lower(), true);
}

ConstantValue HighSubroutine::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)range.upper(), true);
}

ConstantValue LeftSubroutine::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)range.left, true);
}

ConstantValue RightSubroutine::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)range.right, true);
}

ConstantValue SizeSubroutine::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, range.width(), true);
}

ConstantValue IncrementSubroutine::eval(EvalContext&, const Args& args) const {
    ConstantRange range = args[0]->type->getArrayRange();
    return SVInt(32, (uint64_t)(range.isLittleEndian() ? 1 : -1), true);
}

EnumFirstLastMethod::EnumFirstLastMethod(const std::string& name, bool first) :
    SystemSubroutine(name), first(first) {
}

const Type& EnumFirstLastMethod::checkArguments(const BindContext& context,
                                                const Args& args) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, true, args, 0))
        return comp.getErrorType();

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

const Type& EnumNumMethod::checkArguments(const BindContext& context, const Args& args) const {
    auto& comp = context.getCompilation();
    if (!checkArgCount(context, true, args, 0))
        return comp.getErrorType();

    return comp.getIntegerType();
}

ConstantValue EnumNumMethod::eval(EvalContext&, const Args& args) const {
    // Expression isn't actually evaluated here; we know the value to return at compile time.
    const EnumType& type = args.at(0)->type->getCanonicalType().as<EnumType>();
    return SVInt(32, (uint64_t)type.values().size(), true);
}

} // namespace slang::Builtins