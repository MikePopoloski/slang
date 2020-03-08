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
        ASSERT(type.isUnpackedArray());

        auto& elemType = type.getCanonicalType().as<UnpackedArrayType>().elementType;
        if (!elemType.isIntegral()) {
            context.addDiag(diag::ArrayReductionIntegral, args[0]->sourceRange);
            return comp.getErrorType();
        }

        return elemType;
    }

    bool verifyConstant(EvalContext&, const Args&) const final { return true; }
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
            SVInt result = arr.elements()[0].integer();                                        \
            for (auto& elem : arr.elements().subspan(1))                                       \
                result op elem.integer();                                                      \
                                                                                               \
            return result;                                                                     \
        }                                                                                      \
    };

MAKE_REDUCTION_METHOD(Or, "or", |=)
MAKE_REDUCTION_METHOD(And, "and", &=)
MAKE_REDUCTION_METHOD(Xor, "xor", ^=)

#undef MAKE_REDUCTION_METHOD

void registerArrayMethods(Compilation& c) {
#define REGISTER(kind, name, ...) \
    c.addSystemMethod(kind, std::make_unique<name##Method>(__VA_ARGS__))
    REGISTER(SymbolKind::UnpackedArrayType, ArrayOr, );
    REGISTER(SymbolKind::UnpackedArrayType, ArrayAnd, );
    REGISTER(SymbolKind::UnpackedArrayType, ArrayXor, );
#undef REGISTER
}

} // namespace slang::Builtins