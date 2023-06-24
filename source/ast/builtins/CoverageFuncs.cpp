//------------------------------------------------------------------------------
// CoverageFuncs.cpp
// Coverage control functions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Compilation.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast::builtins {

using namespace syntax;

class CoverageNameOrHierFunc : public SystemSubroutine {
public:
    CoverageNameOrHierFunc(const std::string& name, const Type& returnType,
                           unsigned int nameOrHierIndex, size_t requiredArgs = 0,
                           const std::vector<const Type*>& argTypes = {}) :
        SystemSubroutine(name, SubroutineKind::Function),
        argTypes(argTypes), returnType(&returnType), nameOrHierIndex(nameOrHierIndex),
        requiredArgs(requiredArgs) {
        SLANG_ASSERT(requiredArgs <= argTypes.size());
        SLANG_ASSERT(nameOrHierIndex <= argTypes.size());
        SLANG_ASSERT(requiredArgs > nameOrHierIndex);
    };

    const Expression& bindArgument(size_t argIndex, const ASTContext& context,
                                   const ExpressionSyntax& syntax, const Args& args) const final {
        if (argIndex >= argTypes.size())
            return SystemSubroutine::bindArgument(argIndex, context, syntax, args);

        if (argIndex == nameOrHierIndex && NameSyntax::isKind(syntax.kind)) {
            return ArbitrarySymbolExpression::fromSyntax(context.getCompilation(),
                                                         syntax.as<NameSyntax>(), context,
                                                         LookupFlags::AllowRoot);
        }

        return Expression::bindArgument(*argTypes[argIndex], ArgumentDirection::In, syntax,
                                        context);
    }

    const Type& checkArguments(const ASTContext& context, const Args& args, SourceRange range,
                               const Expression*) const final {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, requiredArgs, argTypes.size()))
            return comp.getErrorType();

        auto arg = args[nameOrHierIndex];
        if (arg->kind == ExpressionKind::ArbitrarySymbol) {
            auto& sym = *arg->as<ArbitrarySymbolExpression>().symbol;
            if (sym.isValue()) {
                auto& type = sym.as<ValueSymbol>().getType();
                if (!type.isString()) {
                    context.addDiag(diag::BadSystemSubroutineArg, arg->sourceRange)
                        << type << kindStr();
                    return comp.getErrorType();
                }
            }
            else if (sym.kind != SymbolKind::Root &&
                     (sym.kind != SymbolKind::Instance || !sym.as<InstanceSymbol>().isModule())) {
                if (!context.scope->isUninstantiated())
                    context.addDiag(diag::ExpectedModuleInstance, arg->sourceRange);
                return comp.getErrorType();
            }
        }

        return *returnType;
    }

    ConstantValue eval(EvalContext& context, const Args&, SourceRange range,
                       const CallExpression::SystemCallInfo&) const final {
        notConst(context, range);
        return nullptr;
    }

private:
    std::vector<const Type*> argTypes;
    const Type* returnType;
    unsigned int nameOrHierIndex;
    size_t requiredArgs;
};

void registerCoverageFuncs(Compilation& c) {
#define REGISTER(name, ...) c.addSystemSubroutine(std::make_unique<name>(__VA_ARGS__))
    REGISTER(CoverageNameOrHierFunc, "$coverage_control", c.getIntType(), 3, 4,
             std::vector{&c.getIntType(), &c.getIntType(), &c.getIntType(), &c.getStringType()});
    REGISTER(CoverageNameOrHierFunc, "$coverage_get_max", c.getIntType(), 2, 3,
             std::vector{&c.getIntType(), &c.getIntType(), &c.getStringType()});
    REGISTER(CoverageNameOrHierFunc, "$coverage_get", c.getIntType(), 2, 3,
             std::vector{&c.getIntType(), &c.getIntType(), &c.getStringType()});

    REGISTER(NonConstantFunction, "$coverage_merge", c.getIntType(), 2,
             std::vector{&c.getIntType(), &c.getStringType()});
    REGISTER(NonConstantFunction, "$coverage_save", c.getIntType(), 2,
             std::vector{&c.getIntType(), &c.getStringType()});
    REGISTER(NonConstantFunction, "$get_coverage", c.getRealType());
    REGISTER(NonConstantFunction, "$set_coverage_db_name", c.getVoidType(), 1,
             std::vector{&c.getStringType()});
    REGISTER(NonConstantFunction, "$load_coverage_db", c.getVoidType(), 1,
             std::vector{&c.getStringType()});
#undef REGISTER
}

} // namespace slang::ast::builtins
