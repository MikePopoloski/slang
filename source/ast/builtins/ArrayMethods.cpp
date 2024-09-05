//------------------------------------------------------------------------------
// ArrayMethods.cpp
// Built-in methods on arrays
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "Builtins.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/util/Function.h"

namespace slang::ast::builtins {

using namespace syntax;

static bool isComparable(const Type& type) {
    return type.isNumeric() || type.isString();
}

class ArrayReductionMethod : public SystemSubroutine {
public:
    using Operator = function_ref<void(SVInt&, const SVInt&)>;

    ArrayReductionMethod(const std::string& name, Operator op) :
        SystemSubroutine(name, SubroutineKind::Function), op(op) {
        withClauseMode = WithClauseMode::Iterator;
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression* iterExpr) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        if (iterExpr) {
            if (!iterExpr->type->isIntegral()) {
                context.addDiag(diag::ArrayMethodIntegral, iterExpr->sourceRange) << name;
                return comp.getErrorType();
            }

            return *iterExpr->type;
        }
        else {
            auto elemType = args[0]->type->getArrayElementType();
            SLANG_ASSERT(elemType);

            if (!elemType->isIntegral()) {
                context.addDiag(diag::ArrayMethodIntegral, args[0]->sourceRange) << name;
                return comp.getErrorType();
            }

            return *elemType;
        }
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo& callInfo) const final {
        ConstantValue arr = args[0]->eval(context);
        if (!arr)
            return nullptr;

        auto [iterExpr, iterVar] = callInfo.getIteratorInfo();
        if (iterExpr) {
            SLANG_ASSERT(iterVar);
            if (arr.empty()) {
                auto elemType = iterExpr->type;
                return SVInt(elemType->getBitWidth(), 0, elemType->isSigned());
            }

            auto it = begin(arr);
            auto guard = context.disableCaching();
            auto iterVal = context.createLocal(iterVar, *it);
            ConstantValue cv = iterExpr->eval(context);
            if (!cv)
                return nullptr;

            SVInt result = cv.integer();
            for (++it; it != end(arr); ++it) {
                *iterVal = *it;
                cv = iterExpr->eval(context);
                if (!cv)
                    return nullptr;

                op(result, cv.integer());
            }

            return result;
        }
        else {
            if (arr.empty()) {
                auto elemType = args[0]->type->getArrayElementType();
                return SVInt(elemType->getBitWidth(), 0, elemType->isSigned());
            }

            auto it = begin(arr);
            SVInt result = it->integer();
            for (++it; it != end(arr); ++it)
                op(result, it->integer());

            return result;
        }
    }

private:
    Operator op;
};

class ArraySortMethod : public SystemSubroutine {
public:
    ArraySortMethod(const std::string& name, bool reversed) :
        SystemSubroutine(name, SubroutineKind::Function), reversed(reversed) {
        withClauseMode = WithClauseMode::Iterator;
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression* iterExpr) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        if (!registerLValue(*args[0], context))
            return comp.getErrorType();

        if (iterExpr) {
            if (!isComparable(*iterExpr->type)) {
                context.addDiag(diag::ArrayMethodComparable, iterExpr->sourceRange) << name;
                return comp.getErrorType();
            }
        }
        else {
            auto elemType = args[0]->type->getArrayElementType();
            SLANG_ASSERT(elemType);

            if (!isComparable(*elemType)) {
                context.addDiag(diag::ArrayMethodComparable, args[0]->sourceRange) << name;
                return comp.getErrorType();
            }
        }

        return comp.getVoidType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo& callInfo) const final {
        auto lval = args[0]->evalLValue(context);
        if (!lval)
            return nullptr;

        auto target = lval.resolve();
        if (!target)
            return nullptr;

        auto [iterExpr, iterVar] = callInfo.getIteratorInfo();
        if (iterExpr) {
            SLANG_ASSERT(iterVar);
            auto guard = context.disableCaching();
            auto iterVal = context.createLocal(iterVar);

            auto sortTarget = [&, ie = iterExpr](auto& target) {
                auto pred = [&, ie = ie](ConstantValue& a, ConstantValue& b) {
                    *iterVal = a;
                    ConstantValue cva = ie->eval(context);

                    *iterVal = b;
                    ConstantValue cvb = ie->eval(context);

                    return cva < cvb;
                };

                if (reversed)
                    std::ranges::sort(target.rbegin(), target.rend(), pred);
                else
                    std::ranges::sort(target, pred);
            };

            if (target->isQueue()) {
                sortTarget(*target->queue());
            }
            else {
                auto& vec = std::get<ConstantValue::Elements>(target->getVariant());
                sortTarget(vec);
            }
        }
        else {
            auto sortTarget = [&](auto& target) {
                if (reversed)
                    std::ranges::sort(target.rbegin(), target.rend(), std::less<>{});
                else
                    std::ranges::sort(target, std::less<>{});
            };

            if (target->isQueue()) {
                sortTarget(*target->queue());
            }
            else {
                auto& vec = std::get<ConstantValue::Elements>(target->getVariant());
                sortTarget(vec);
            }
        }

        return nullptr;
    }

private:
    bool reversed;
};

class ArrayReverseMethod : public SystemSubroutine {
public:
    ArrayReverseMethod() : SystemSubroutine("reverse", SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        if (!registerLValue(*args[0], context))
            return comp.getErrorType();

        return comp.getVoidType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto lval = args[0]->evalLValue(context);
        if (!lval)
            return nullptr;

        auto target = lval.resolve();
        if (!target)
            return nullptr;

        if (target->isQueue())
            std::ranges::reverse(*target->queue());
        else
            std::ranges::reverse(std::get<ConstantValue::Elements>(target->getVariant()));

        return nullptr;
    }
};

class ArrayLocatorMethod : public SystemSubroutine {
public:
    enum Mode { All, First, Last } mode;
    bool isIndexed;

    ArrayLocatorMethod(const std::string& name, Mode mode, bool isIndexed) :
        SystemSubroutine(name, SubroutineKind::Function), mode(mode), isIndexed(isIndexed) {
        withClauseMode = WithClauseMode::Iterator;
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression* iterExpr) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        if (!iterExpr) {
            context.addDiag(diag::ArrayLocatorWithClause, range) << name;
            return comp.getErrorType();
        }

        if (!context.requireBooleanConvertible(*iterExpr))
            return comp.getErrorType();

        auto arrayType = args[0]->type;
        if (isIndexed) {
            if (arrayType->isAssociativeArray()) {
                auto indexType = arrayType->getAssociativeIndexType();
                if (!indexType) {
                    context.addDiag(diag::AssociativeWildcardNotAllowed, range) << name;
                    return comp.getErrorType();
                }
                return *comp.emplace<QueueType>(*indexType, 0u);
            }
            return *comp.emplace<QueueType>(comp.getIntType(), 0u);
        }

        return *comp.emplace<QueueType>(*arrayType->getArrayElementType(), 0u);
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo& callInfo) const final {
        ConstantValue arr = args[0]->eval(context);
        if (!arr)
            return nullptr;

        auto [iterExpr, iterVar] = callInfo.getIteratorInfo();
        auto guard = context.disableCaching();
        auto iterVal = context.createLocal(iterVar);

        SVQueue results;
        if (arr.isMap()) {
            auto doFind = [&, ie = iterExpr](auto it, auto end) {
                for (; it != end; it++) {
                    *iterVal = it->second;
                    ConstantValue cv = ie->eval(context);
                    if (cv.isTrue()) {
                        if (isIndexed)
                            results.emplace_back(it->first);
                        else
                            results.emplace_back(it->second);

                        if (mode != All)
                            break;
                    }
                }
            };

            auto& cont = *arr.map();
            if (mode == Last)
                doFind(std::rbegin(cont), std::rend(cont));
            else
                doFind(std::begin(cont), std::end(cont));
        }
        else {
            auto doFind = [&, ie = iterExpr](auto begin, auto end) {
                for (auto it = begin; it != end; it++) {
                    *iterVal = *it;
                    ConstantValue cv = ie->eval(context);
                    if (cv.isTrue()) {
                        if (isIndexed) {
                            auto dist = std::ranges::distance(begin, it);
                            if (mode == Last)
                                dist = std::ranges::distance(begin, end) - dist - 1;

                            results.emplace_back(SVInt(32, (uint64_t)dist, true));
                        }
                        else {
                            results.emplace_back(*it);
                        }

                        if (mode != All)
                            break;
                    }
                }
            };

            auto find = [&](auto& cont) {
                if (mode == Last)
                    doFind(std::rbegin(cont), std::rend(cont));
                else
                    doFind(std::begin(cont), std::end(cont));
            };

            if (arr.isQueue())
                find(*arr.queue());
            else
                find(std::get<ConstantValue::Elements>(arr.getVariant()));
        }

        return results;
    }
};

class ArrayMinMaxMethod : public SystemSubroutine {
public:
    ArrayMinMaxMethod(const std::string& name, bool isMin) :
        SystemSubroutine(name, SubroutineKind::Function), isMin(isMin) {
        withClauseMode = WithClauseMode::Iterator;
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression* iterExpr) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        auto elemType = args[0]->type->getArrayElementType();
        SLANG_ASSERT(elemType);

        if (iterExpr) {
            if (!isComparable(*iterExpr->type)) {
                context.addDiag(diag::ArrayMethodComparable, iterExpr->sourceRange) << name;
                return comp.getErrorType();
            }
        }
        else if (!isComparable(*elemType)) {
            context.addDiag(diag::ArrayMethodComparable, args[0]->sourceRange) << name;
            return comp.getErrorType();
        }

        return *comp.emplace<QueueType>(*elemType, 0u);
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo& callInfo) const final {
        ConstantValue arr = args[0]->eval(context);
        if (!arr)
            return nullptr;

        SVQueue result;
        if (arr.empty())
            return result;

        auto [iterExpr, iterVar] = callInfo.getIteratorInfo();
        if (iterExpr) {
            SLANG_ASSERT(iterVar);

            auto it = begin(arr);
            auto guard = context.disableCaching();
            auto iterVal = context.createLocal(iterVar, *it);
            ConstantValue elem = *it;
            ConstantValue val = iterExpr->eval(context);

            for (++it; it != end(arr); ++it) {
                *iterVal = *it;
                auto cv = iterExpr->eval(context);

                if (isMin) {
                    if (cv < val) {
                        val = cv;
                        elem = *it;
                    }
                }
                else {
                    if (val < cv) {
                        val = cv;
                        elem = *it;
                    }
                }
            }
            result.emplace_back(std::move(elem));
        }
        else {
            auto it = begin(arr);
            ConstantValue elem = *it;
            for (++it; it != end(arr); ++it) {
                if (isMin) {
                    if (*it < elem)
                        elem = *it;
                }
                else {
                    if (elem < *it)
                        elem = *it;
                }
            }
            result.emplace_back(std::move(elem));
        }

        return result;
    }

private:
    bool isMin;
};

class ArrayUniqueMethod : public SystemSubroutine {
public:
    ArrayUniqueMethod(const std::string& name, bool isIndexed) :
        SystemSubroutine(name, SubroutineKind::Function), isIndexed(isIndexed) {
        withClauseMode = WithClauseMode::Iterator;
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        auto arrayType = args[0]->type;
        if (isIndexed) {
            if (arrayType->isAssociativeArray()) {
                auto indexType = arrayType->getAssociativeIndexType();
                if (!indexType) {
                    context.addDiag(diag::AssociativeWildcardNotAllowed, range) << name;
                    return comp.getErrorType();
                }
                return *comp.emplace<QueueType>(*indexType, 0u);
            }
            return *comp.emplace<QueueType>(comp.getIntType(), 0u);
        }

        return *comp.emplace<QueueType>(*arrayType->getArrayElementType(), 0u);
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo& callInfo) const final {
        ConstantValue arr = args[0]->eval(context);
        if (!arr)
            return nullptr;

        SVQueue result;

        auto [iterExpr, iterVar] = callInfo.getIteratorInfo();
        if (iterExpr) {
            SLANG_ASSERT(iterVar);
            auto guard = context.disableCaching();
            auto iterVal = context.createLocal(iterVar);

            uint32_t index = 0;
            flat_hash_set<ConstantValue> seen;
            for (auto it = begin(arr); it != end(arr); ++it, ++index) {
                *iterVal = *it;
                auto cv = iterExpr->eval(context);
                if (seen.emplace(cv).second) {
                    if (isIndexed && !arr.isMap())
                        result.emplace_back(SVInt(32, index, true));
                    else if (isIndexed)
                        result.emplace_back(it.key());
                    else
                        result.emplace_back(std::move(*it));
                }
            }
        }
        else {
            uint32_t index = 0;
            flat_hash_set<ConstantValue> seen;
            for (auto it = begin(arr); it != end(arr); ++it, ++index) {
                if (seen.emplace(*it).second) {
                    if (isIndexed && !arr.isMap())
                        result.emplace_back(SVInt(32, index, true));
                    else if (isIndexed)
                        result.emplace_back(it.key());
                    else
                        result.emplace_back(std::move(*it));
                }
            }
        }

        return result;
    }

private:
    bool isIndexed;
};

class ArraySizeMethod : public SimpleSystemSubroutine {
public:
    ArraySizeMethod(const Builtins& builtins, const std::string& name) :
        SimpleSystemSubroutine(name, SubroutineKind::Function, 0, {}, builtins.intType, true) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto val = args[0]->eval(context);
        if (!val)
            return nullptr;

        return SVInt(32, val.size(), true);
    }
};

class DynArrayDeleteMethod : public SimpleSystemSubroutine {
public:
    explicit DynArrayDeleteMethod(const Builtins& builtins) :
        SimpleSystemSubroutine("delete", SubroutineKind::Function, 0, {}, builtins.voidType, true,
                               /* isFirstArgLValue */ true) {}

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
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

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        // Argument type comes from the index type of the previous argument.
        if (argIndex == 1) {
            auto indexType = args[0]->type->getAssociativeIndexType();
            if (indexType) {
                return Expression::bindArgument(*indexType, ArgumentDirection::In, {}, syntax,
                                                context);
            }
        }

        return SystemSubroutine::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 1))
            return comp.getErrorType();

        if (!registerLValue(*args[0], context))
            return comp.getErrorType();

        if (args.size() > 1) {
            auto& type = *args[0]->type;
            auto indexType = type.getAssociativeIndexType();
            if (!indexType && !args[1]->type->isIntegral())
                return badArg(context, *args[1]);
        }

        return comp.getVoidType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
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
};

class AssocArrayExistsMethod : public SystemSubroutine {
public:
    AssocArrayExistsMethod() : SystemSubroutine("exists", SubroutineKind::Function) {}

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        // Argument type comes from the index type of the previous argument.
        if (argIndex == 1) {
            auto indexType = args[0]->type->getAssociativeIndexType();
            if (indexType) {
                return Expression::bindArgument(*indexType, ArgumentDirection::In, {}, syntax,
                                                context);
            }
        }

        return SystemSubroutine::bindArgument(argIndex, context, syntax, args);
    }

    // Return type is 'int' but the actual value is always either 0 or 1
    std::optional<bitwidth_t> getEffectiveWidth() const final { return 1; }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 1, 1))
            return comp.getErrorType();

        auto& type = *args[0]->type;
        auto indexType = type.getAssociativeIndexType();
        if (!indexType && !args[1]->type->isIntegral())
            return badArg(context, *args[1]);

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto array = args[0]->eval(context);
        auto index = args[1]->eval(context);
        if (!array || !index)
            return nullptr;

        bool exists = array.map()->count(index);
        return SVInt(32, exists ? 1 : 0, true);
    }
};

class AssocArrayTraversalMethod : public SystemSubroutine {
public:
    explicit AssocArrayTraversalMethod(const std::string& name) :
        SystemSubroutine(name, SubroutineKind::Function) {
        hasOutputArgs = true;
    }

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        // Argument type comes from the index type of the previous argument.
        if (argIndex == 1) {
            auto indexType = args[0]->type->getAssociativeIndexType();
            if (indexType) {
                return Expression::bindArgument(*indexType, ArgumentDirection::Ref, {}, syntax,
                                                context);
            }
        }

        return SystemSubroutine::bindArgument(argIndex, context, syntax, args);
    }

    // Return type is 'int' but the actual value is always either 0 or 1
    std::optional<bitwidth_t> getEffectiveWidth() const final { return 1; }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 1, 1))
            return comp.getErrorType();

        auto& type = *args[0]->type;
        auto indexType = type.getAssociativeIndexType();
        if (!indexType) {
            context.addDiag(diag::AssociativeWildcardNotAllowed, range) << name;
            return context.getCompilation().getErrorType();
        }

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class QueuePopMethod : public SystemSubroutine {
public:
    QueuePopMethod(const std::string& name, bool front) :
        SystemSubroutine(name, SubroutineKind::Function), front(front) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        if (!registerLValue(*args[0], context))
            return comp.getErrorType();

        return *args[0]->type->getArrayElementType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto lval = args[0]->evalLValue(context);
        if (!lval)
            return nullptr;

        auto target = lval.resolve();
        SLANG_ASSERT(target && target->isQueue());

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

private:
    bool front;
};

class QueuePushMethod : public SystemSubroutine {
public:
    QueuePushMethod(const std::string& name, bool front) :
        SystemSubroutine(name, SubroutineKind::Function), front(front) {}

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        // Argument type comes from the element type of the queue.
        if (argIndex == 1) {
            auto elemType = args[0]->type->getArrayElementType();
            if (elemType) {
                return Expression::bindArgument(*elemType, ArgumentDirection::In, {}, syntax,
                                                context);
            }
        }

        return SystemSubroutine::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 1, 1))
            return comp.getErrorType();

        if (!registerLValue(*args[0], context))
            return comp.getErrorType();

        return comp.getVoidType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto lval = args[0]->evalLValue(context);
        auto cv = args[1]->eval(context);
        if (!lval || !cv)
            return nullptr;

        auto target = lval.resolve();
        SLANG_ASSERT(target && target->isQueue());

        auto& q = *target->queue();
        if (front)
            q.push_front(std::move(cv));
        else
            q.push_back(std::move(cv));

        q.resizeToBound();
        return nullptr;
    }

private:
    bool front;
};

class QueueInsertMethod : public SystemSubroutine {
public:
    QueueInsertMethod() : SystemSubroutine("insert", SubroutineKind::Function) {}

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        // Argument type comes from the element type of the queue.
        if (argIndex == 2) {
            auto elemType = args[0]->type->getArrayElementType();
            if (elemType) {
                return Expression::bindArgument(*elemType, ArgumentDirection::In, {}, syntax,
                                                context);
            }
        }

        return SystemSubroutine::bindArgument(argIndex, context, syntax, args);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 2, 2))
            return comp.getErrorType();

        if (!registerLValue(*args[0], context))
            return comp.getErrorType();

        if (!args[1]->type->isIntegral())
            return badArg(context, *args[1]);

        return comp.getVoidType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto lval = args[0]->evalLValue(context);
        auto ci = args[1]->eval(context);
        auto cv = args[2]->eval(context);
        if (!lval || !ci || !cv)
            return nullptr;

        auto target = lval.resolve();
        SLANG_ASSERT(target && target->isQueue());

        auto& q = *target->queue();
        std::optional<int32_t> index = ci.integer().as<int32_t>();
        if (!index || *index < 0 || size_t(*index) >= q.size() + 1) {
            context.addDiag(diag::ConstEvalDynamicArrayIndex, args[1]->sourceRange)
                << ci << *args[0]->type << q.size() + 1;
            return nullptr;
        }

        q.insert(q.begin() + *index, std::move(cv));
        q.resizeToBound();
        return nullptr;
    }
};

class QueueDeleteMethod : public SystemSubroutine {
public:
    QueueDeleteMethod() : SystemSubroutine("delete", SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 1))
            return comp.getErrorType();

        if (!registerLValue(*args[0], context))
            return comp.getErrorType();

        if (args.size() > 1) {
            if (!args[1]->type->isIntegral())
                return badArg(context, *args[1]);
        }

        return comp.getVoidType();
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo&) const final {
        auto lval = args[0]->evalLValue(context);
        if (!lval)
            return nullptr;

        auto target = lval.resolve();
        SLANG_ASSERT(target && target->isQueue());
        auto& q = *target->queue();

        // If no arguments, clear the queue.
        if (args.size() == 1) {
            q.clear();
            return nullptr;
        }

        auto ci = args[1]->eval(context);
        std::optional<int32_t> index = ci.integer().as<int32_t>();
        if (!index || *index < 0 || size_t(*index) >= q.size()) {
            context.addDiag(diag::ConstEvalDynamicArrayIndex, args[1]->sourceRange)
                << ci << *args[0]->type << q.size();
            return nullptr;
        }

        q.erase(q.begin() + *index);
        return nullptr;
    }
};

class IteratorIndexMethod : public SystemSubroutine {
public:
    IteratorIndexMethod() : SystemSubroutine("index", SubroutineKind::Function) {}

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 1))
            return comp.getErrorType();

        if (args.size() > 1 && !args[1]->type->isIntegral())
            return badArg(context, *args[1]);

        auto& iterator = args[0]->as<NamedValueExpression>().symbol.as<IteratorSymbol>();
        if (iterator.arrayType.isAssociativeArray()) {
            auto indexType = iterator.arrayType.getAssociativeIndexType();
            if (!indexType) {
                context.addDiag(diag::AssociativeWildcardNotAllowed, range) << name;
                return comp.getErrorType();
            }
            return *indexType;
        }

        return comp.getIntType();
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }
};

class ArrayMapMethod : public SystemSubroutine {
public:
    ArrayMapMethod() : SystemSubroutine("map", SubroutineKind::Function) {
        withClauseMode = WithClauseMode::Iterator;
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression* iterExpr) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, true, args, range, 0, 0))
            return comp.getErrorType();

        if (!iterExpr) {
            context.addDiag(diag::ArrayLocatorWithClause, range) << name;
            return comp.getErrorType();
        }

        auto languageVersion = comp.languageVersion();
        if (languageVersion < LanguageVersion::v1800_2023)
            context.addDiag(diag::WrongLanguageVersion, range) << toString(languageVersion);

        auto& arrayType = args[0]->type->getCanonicalType();
        auto& elemType = *iterExpr->type;
        switch (arrayType.kind) {
            case SymbolKind::FixedSizeUnpackedArrayType: {
                auto& fsuat = arrayType.as<FixedSizeUnpackedArrayType>();
                return FixedSizeUnpackedArrayType::fromDim(*context.scope, elemType, fsuat.range,
                                                           iterExpr->sourceRange);
            }
            case SymbolKind::DynamicArrayType:
                return *comp.emplace<DynamicArrayType>(elemType);
            case SymbolKind::AssociativeArrayType: {
                auto& aat = arrayType.as<AssociativeArrayType>();
                return *comp.emplace<AssociativeArrayType>(elemType, aat.indexType);
            }
            case SymbolKind::QueueType: {
                auto& qt = arrayType.as<QueueType>();
                return *comp.emplace<QueueType>(elemType, qt.maxBound);
            }
            default:
                SLANG_UNREACHABLE;
        }
    }

    ConstantValue eval(EvalContext& context, const Args& args, SourceRange,
                       const CallExpression::SystemCallInfo& callInfo) const final {
        ConstantValue arr = args[0]->eval(context);
        if (!arr)
            return nullptr;

        auto [iterExpr, iterVar] = callInfo.getIteratorInfo();
        auto guard = context.disableCaching();
        auto iterVal = context.createLocal(iterVar);

        if (arr.isMap()) {
            AssociativeArray results;
            for (auto& [key, val] : *arr.map()) {
                *iterVal = val;
                ConstantValue cv = iterExpr->eval(context);
                if (!cv)
                    return nullptr;

                results.emplace(key, std::move(cv));
            }
            return results;
        }
        else {
            auto doMap = [&, ie = iterExpr](auto& container, auto& results) {
                for (auto& elem : container) {
                    *iterVal = elem;
                    ConstantValue cv = ie->eval(context);
                    if (!cv)
                        return false;

                    results.emplace_back(std::move(cv));
                }
                return true;
            };

            if (arr.isQueue()) {
                SVQueue results;
                if (!doMap(*arr.queue(), results))
                    return nullptr;
                return results;
            }
            else {
                ConstantValue::Elements results;
                if (!doMap(std::get<ConstantValue::Elements>(arr.getVariant()), results))
                    return nullptr;
                return results;
            }
        }
    }
};

void Builtins::registerArrayMethods() {
#define REGISTER(kind, name, ...) addSystemMethod(kind, std::make_shared<name##Method>(__VA_ARGS__))

    for (auto kind : {SymbolKind::FixedSizeUnpackedArrayType, SymbolKind::DynamicArrayType,
                      SymbolKind::AssociativeArrayType, SymbolKind::QueueType}) {
        REGISTER(kind, ArrayReduction, "or", [](auto& l, auto& r) { l |= r; });
        REGISTER(kind, ArrayReduction, "and", [](auto& l, auto& r) { l &= r; });
        REGISTER(kind, ArrayReduction, "xor", [](auto& l, auto& r) { l ^= r; });
        REGISTER(kind, ArrayReduction, "sum", [](auto& l, auto& r) { l += r; });
        REGISTER(kind, ArrayReduction, "product", [](auto& l, auto& r) { l *= r; });

        REGISTER(kind, ArrayLocator, "find", ArrayLocatorMethod::All, false);
        REGISTER(kind, ArrayLocator, "find_index", ArrayLocatorMethod::All, true);
        REGISTER(kind, ArrayLocator, "find_first", ArrayLocatorMethod::First, false);
        REGISTER(kind, ArrayLocator, "find_first_index", ArrayLocatorMethod::First, true);
        REGISTER(kind, ArrayLocator, "find_last", ArrayLocatorMethod::Last, false);
        REGISTER(kind, ArrayLocator, "find_last_index", ArrayLocatorMethod::Last, true);

        REGISTER(kind, ArrayMinMax, "min", true);
        REGISTER(kind, ArrayMinMax, "max", false);

        REGISTER(kind, ArrayUnique, "unique", false);
        REGISTER(kind, ArrayUnique, "unique_index", true);

        REGISTER(kind, ArrayMap, );
    }

    for (auto kind :
         {SymbolKind::DynamicArrayType, SymbolKind::AssociativeArrayType, SymbolKind::QueueType}) {
        REGISTER(kind, ArraySize, *this, "size");
    }

    for (auto kind : {SymbolKind::FixedSizeUnpackedArrayType, SymbolKind::DynamicArrayType,
                      SymbolKind::QueueType}) {
        REGISTER(kind, ArraySort, "sort", false);
        REGISTER(kind, ArraySort, "rsort", true);
        REGISTER(kind, ArrayReverse, );

        addSystemMethod(kind, std::make_shared<NonConstantFunction>(
                                  "shuffle", voidType, 0, std::vector<const Type*>{}, true));
    }

    // Associative arrays also alias "size" to "num" for some reason.
    REGISTER(SymbolKind::AssociativeArrayType, ArraySize, *this, "num");

    // "delete" methods
    REGISTER(SymbolKind::DynamicArrayType, DynArrayDelete, *this);
    REGISTER(SymbolKind::AssociativeArrayType, AssocArrayDelete, );
    REGISTER(SymbolKind::QueueType, QueueDelete, );

    // Associative array methods.
    REGISTER(SymbolKind::AssociativeArrayType, AssocArrayExists, );
    REGISTER(SymbolKind::AssociativeArrayType, AssocArrayTraversal, "first");
    REGISTER(SymbolKind::AssociativeArrayType, AssocArrayTraversal, "last");
    REGISTER(SymbolKind::AssociativeArrayType, AssocArrayTraversal, "next");
    REGISTER(SymbolKind::AssociativeArrayType, AssocArrayTraversal, "prev");

    // Queue methods
    REGISTER(SymbolKind::QueueType, QueuePop, "pop_front", true);
    REGISTER(SymbolKind::QueueType, QueuePop, "pop_back", false);
    REGISTER(SymbolKind::QueueType, QueuePush, "push_front", true);
    REGISTER(SymbolKind::QueueType, QueuePush, "push_back", false);
    REGISTER(SymbolKind::QueueType, QueueInsert, );

    // Iterator methods
    REGISTER(SymbolKind::Iterator, IteratorIndex, );
}

} // namespace slang::ast::builtins
