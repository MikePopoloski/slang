//------------------------------------------------------------------------------
// ArrayMethods.cpp
// Built-in methods on arrays
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/util/Function.h"

namespace slang::Builtins {

class ArrayReductionMethod : public SystemSubroutine {
public:
    using Operator = function_ref<void(SVInt&, const SVInt&)>;

    ArrayReductionMethod(const std::string& name, Operator op) :
        SystemSubroutine(name, SubroutineKind::Function), op(op) {}

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

    ConstantValue eval(const Scope&, EvalContext& context, const Args& args) const final {
        ConstantValue arr = args[0]->eval(context);
        if (!arr)
            return nullptr;

        auto elemType = args[0]->type->getArrayElementType();
        if (arr.empty())
            return SVInt(elemType->getBitWidth(), 0, elemType->isSigned());

        auto it = begin(arr);
        SVInt result = it->integer();
        for (++it; it != end(arr); ++it)
            op(result, it->integer());

        return result;
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }

private:
    Operator op;
};

class ArraySizeMethod : public SimpleSystemSubroutine {
public:
    ArraySizeMethod(Compilation& comp, const std::string& name) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, 0, {}, comp.getIntType(), true) {}

    ConstantValue eval(const Scope&, EvalContext& context, const Args& args) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        return SVInt(32, val.size(), true);
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

class QueuePopMethod : public SystemSubroutine {
public:
    QueuePopMethod(const std::string& name, bool front) :
        SystemSubroutine(name, SubroutineKind::Function), front(front) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        return *args[0]->type->getArrayElementType();
    }

    ConstantValue eval(const Scope&, EvalContext& context, const Args& args) const final {
        auto lval = args[0]->evalLValue(context);
        if (!lval)
            return nullptr;

        auto target = lval.resolve();
        ASSERT(target && target->isQueue());

        auto& q = *target->queue();
        if (q.empty()) {
            context.addDiag(diag::ConstEvalEmptyQueue, args[0]->sourceRange);
            return args[0]->type->getArrayElementType()->getDefaultValue();
        }

        ConstantValue result = front ? std::move(q.front()) : std::move(q.back());
        if (front)
            q.pop_front();
        else
            q.pop_back();

        return result;
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }

private:
    bool front;
};

class QueuePushMethod : public SystemSubroutine {
public:
    QueuePushMethod(const std::string& name, bool front) :
        SystemSubroutine(name, SubroutineKind::Function), front(front) {}

    const Expression& bindArgument(size_t argIndex, const BindContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        // Argument type comes from the element type of the queue.
        if (argIndex == 1) {
            auto elemType = args[0]->type->getArrayElementType();
            if (elemType)
                return Expression::bindArgument(*elemType, ArgumentDirection::In, syntax, context);
        }

        return SystemSubroutine::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 1, 1))
            return comp.getErrorType();

        return comp.getVoidType();
    }

    ConstantValue eval(const Scope&, EvalContext& context, const Args& args) const final {
        auto lval = args[0]->evalLValue(context);
        auto cv = args[1]->eval(context);
        if (!lval || !cv)
            return nullptr;

        auto target = lval.resolve();
        ASSERT(target && target->isQueue());

        auto& q = *target->queue();
        if (front)
            q.push_front(std::move(cv));
        else
            q.push_back(std::move(cv));

        return nullptr;
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }

private:
    bool front;
};

class QueueInsertMethod : public SystemSubroutine {
public:
    QueueInsertMethod() : SystemSubroutine("insert", SubroutineKind::Function) {}

    const Expression& bindArgument(size_t argIndex, const BindContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        // Argument type comes from the element type of the queue.
        if (argIndex == 2) {
            auto elemType = args[0]->type->getArrayElementType();
            if (elemType)
                return Expression::bindArgument(*elemType, ArgumentDirection::In, syntax, context);
        }

        return SystemSubroutine::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 2, 2))
            return comp.getErrorType();

        if (!args[1]->type->isIntegral())
            return badArg(context, *args[1]);

        return comp.getVoidType();
    }

    ConstantValue eval(const Scope&, EvalContext& context, const Args& args) const final {
        auto lval = args[0]->evalLValue(context);
        auto ci = args[1]->eval(context);
        auto cv = args[2]->eval(context);
        if (!lval || !ci || !cv)
            return nullptr;

        auto target = lval.resolve();
        ASSERT(target && target->isQueue());

        auto& q = *target->queue();
        optional<int32_t> index = ci.integer().as<int32_t>();
        if (!index || *index < 0 || size_t(*index) >= q.size() + 1) {
            context.addDiag(diag::ConstEvalDynamicArrayIndex, args[1]->sourceRange)
                << ci << *args[0]->type << q.size() + 1;
            return nullptr;
        }

        q.insert(q.begin() + *index, std::move(cv));
        return nullptr;
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }
};

class QueueDeleteMethod : public SystemSubroutine {
public:
    QueueDeleteMethod() : SystemSubroutine("delete", SubroutineKind::Function) {}

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 1))
            return comp.getErrorType();

        if (args.size() > 1) {
            if (!args[1]->type->isIntegral())
                return badArg(context, *args[1]);
        }

        return comp.getVoidType();
    }

    ConstantValue eval(const Scope&, EvalContext& context, const Args& args) const final {
        auto lval = args[0]->evalLValue(context);
        if (!lval)
            return nullptr;

        auto target = lval.resolve();
        ASSERT(target && target->isQueue());
        auto& q = *target->queue();

        // If no arguments, clear the queue.
        if (args.size() == 1) {
            q.clear();
            return nullptr;
        }

        auto ci = args[1]->eval(context);
        optional<int32_t> index = ci.integer().as<int32_t>();
        if (!index || *index < 0 || size_t(*index) >= q.size()) {
            context.addDiag(diag::ConstEvalDynamicArrayIndex, args[1]->sourceRange)
                << ci << *args[0]->type << q.size();
            return nullptr;
        }

        q.erase(q.begin() + *index);
        return nullptr;
    }

    bool verifyConstant(EvalContext&, const Args&, SourceRange) const final { return true; }
};

void registerArrayMethods(Compilation& c) {
#define REGISTER(kind, name, ...) \
    c.addSystemMethod(kind, std::make_unique<name##Method>(__VA_ARGS__))

    for (auto kind : { SymbolKind::FixedSizeUnpackedArrayType, SymbolKind::DynamicArrayType,
                       SymbolKind::AssociativeArrayType, SymbolKind::QueueType }) {
        REGISTER(kind, ArrayReduction, "or", [](auto& l, auto& r) { l |= r; });
        REGISTER(kind, ArrayReduction, "and", [](auto& l, auto& r) { l &= r; });
        REGISTER(kind, ArrayReduction, "xor", [](auto& l, auto& r) { l ^= r; });
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
    REGISTER(SymbolKind::QueueType, QueueDelete, );

    // Queue methods
    REGISTER(SymbolKind::QueueType, QueuePop, "pop_front", true);
    REGISTER(SymbolKind::QueueType, QueuePop, "pop_back", false);
    REGISTER(SymbolKind::QueueType, QueuePush, "push_front", true);
    REGISTER(SymbolKind::QueueType, QueuePush, "push_back", false);
    REGISTER(SymbolKind::QueueType, QueueInsert, );
}

} // namespace slang::Builtins