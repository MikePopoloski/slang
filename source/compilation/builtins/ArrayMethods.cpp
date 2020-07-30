//------------------------------------------------------------------------------
// ArrayMethods.cpp
// Built-in methods on arrays
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"

namespace slang::Builtins {

class ArrayReductionMethod : public SystemSubroutine {
public:
    explicit ArrayReductionMethod(const std::string& name) :
        SystemSubroutine(name, SubroutineKind::Function) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        auto& type = *args[0]->type;
        auto elemType = type.getArrayElementType();
        ASSERT(elemType);

        if (!elemType->isIntegral()) {
            context.addDiag(diag::ArrayReductionIntegral, args[0]->sourceRange);
            return comp.getErrorType();
        }

        return *elemType;
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }
};

#define MAKE_REDUCTION_METHOD(typeName, sourceName, op)                                        \
    class Array##typeName##Method : public ArrayReductionMethod {                              \
    public:                                                                                    \
        Array##typeName##Method() : ArrayReductionMethod(sourceName) {}                        \
                                                                                               \
        ConstantValue eval(const Scope&, EvalContext& context, const Args& args) const final { \
            ConstantValue arr = args[0]->eval(context);                                        \
            if (!arr)                                                                          \
                return nullptr;                                                                \
                                                                                               \
            if (arr.isQueue()) {                                                               \
                auto& q = *arr.queue();                                                        \
                SVInt result = q[0].integer();                                                 \
                for (size_t i = 1; i < q.size(); i++)                                          \
                    result op q[i].integer();                                                  \
                                                                                               \
                return result;                                                                 \
            }                                                                                  \
            else {                                                                             \
                SVInt result = arr.elements()[0].integer();                                    \
                for (auto& elem : arr.elements().subspan(1))                                   \
                    result op elem.integer();                                                  \
                                                                                               \
                return result;                                                                 \
            }                                                                                  \
        }                                                                                      \
    };

MAKE_REDUCTION_METHOD(Or, "or", |=)
MAKE_REDUCTION_METHOD(And, "and", &=)
MAKE_REDUCTION_METHOD(Xor, "xor", ^=)

#undef MAKE_REDUCTION_METHOD

class ArraySizeMethod : public SimpleSystemSubroutine {
public:
    ArraySizeMethod(Compilation& comp, const std::string& name) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, 0, {}, comp.getIntType(), true) {}

    ConstantValue eval(const Scope&, EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        size_t size;
        if (val.isMap())
            size = val.map()->size();
        else if (val.isQueue())
            size = val.queue()->size();
        else
            size = val.elements().size();

        return SVInt(32, size, true);
    }
};

class DynArrayDeleteMethod : public SimpleSystemSubroutine {
public:
    explicit DynArrayDeleteMethod(Compilation& comp) :
        SimpleSystemSubroutine("delete", SubroutineKind::Function, 0, {}, comp.getVoidType(),
                               true) {}

    ConstantValue eval(const Scope&, EvalContext& context, const Args& args) const final {
        auto lval = args[0]->evalLValue(context);
        if (!lval)
            return nullptr;

        lval.store(args[0]->type->getDefaultValue());
        return nullptr;
    }
};

class AssocArrayDeleteMethod : public SystemSubroutine {
public:
    AssocArrayDeleteMethod() : SystemSubroutine("delete", SubroutineKind::Function) {}

    const Expression& bindArgument(size_t argIndex, const BindContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        // Argument type comes from the index type of the previous argument.
        if (argIndex == 1) {
            auto indexType = args[0]->type->getAssociativeIndexType();
            if (indexType)
                return Expression::bindArgument(*indexType, ArgumentDirection::In, syntax, context);
        }

        return SystemSubroutine::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 1))
            return comp.getErrorType();

        if (args.size() > 1) {
            auto& type = *args[0]->type;
            auto indexType = type.getAssociativeIndexType();
            if (!indexType && !args[1]->type->isIntegral())
                return badArg(context, *args[1]);
        }

        return comp.getVoidType();
    }

    ConstantValue eval(const Scope&, EvalContext& context, const Args& args) const final {
        auto lval = args[0]->evalLValue(context);
        if (!lval)
            return nullptr;

        if (args.size() > 1) {
            auto index = args[1]->eval(context);
            if (!index)
                return nullptr;

            auto target = lval.resolve();
            if (target && target->isMap()) {
                // Try to erase the element -- no warning if it doesn't exist.
                target->map()->erase(index);
            }
        }
        else {
            // No argument means we should empty the array.
            lval.store(args[0]->type->getDefaultValue());
        }
        return nullptr;
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }
};

void registerArrayMethods(Compilation& c) {
#define REGISTER(kind, name, ...) \
    c.addSystemMethod(kind, std::make_unique<name##Method>(__VA_ARGS__))

    for (auto kind : { SymbolKind::FixedSizeUnpackedArrayType, SymbolKind::DynamicArrayType,
                       SymbolKind::AssociativeArrayType, SymbolKind::QueueType }) {
        REGISTER(kind, ArrayOr, );
        REGISTER(kind, ArrayAnd, );
        REGISTER(kind, ArrayXor, );
    }

    for (auto kind : { SymbolKind::DynamicArrayType, SymbolKind::AssociativeArrayType,
                       SymbolKind::QueueType }) {
        REGISTER(kind, ArraySize, c, "size");
    }

    // Associative arrays also alias "size" to "num" for some reason.
    REGISTER(SymbolKind::AssociativeArrayType, ArraySize, c, "num");

    // "delete" methods
    REGISTER(SymbolKind::DynamicArrayType, DynArrayDelete, c);
    REGISTER(SymbolKind::AssociativeArrayType, AssocArrayDelete, );
}

} // namespace slang::Builtins