//------------------------------------------------------------------------------
// CoverageFuncs.cpp
// Coverage control functions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/MiscExpressions.h"
#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/SysFuncsDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::Builtins {

class CoverageNameOrHierFunc : public SystemSubroutine {
public:

    CoverageNameOrHierFunc(const std::string& name, const Type& returnType, unsigned int nameOrHierIndex,
                           size_t requiredArgs = 0, const std::vector<const Type*>& argTypes = {}) :
        SystemSubroutine(name, SubroutineKind::Function),
        argTypes(argTypes), returnType(&returnType),
        nameOrHierIndex(nameOrHierIndex), requiredArgs(requiredArgs) {
        ASSERT(requiredArgs <= argTypes.size());
        ASSERT(nameOrHierIndex <= argTypes.size());
    };

    virtual const Expression& bindArgument(size_t argIndex, const BindContext& context,
                                           const ExpressionSyntax& syntax, const Args& args) const final {
        const BindContext* ctx = &context;

        if (argIndex >= argTypes.size())
            return SystemSubroutine::bindArgument(argIndex, *ctx, syntax, args);

        if (argIndex == nameOrHierIndex && NameSyntax::isKind(syntax.kind)) {
            return HierarchicalReferenceExpression::fromSyntax(context.getCompilation(),
               syntax.as<NameSyntax>(), context);
        }

        return Expression::bindArgument(*argTypes[argIndex], ArgumentDirection::In, syntax, *ctx);
    }

    const Type& checkArguments(const BindContext& context, const Args& args,
                               SourceRange range, const Expression*) const {
        auto& comp = context.getCompilation();
        if (!checkArgCount(context, false, args, range, requiredArgs, argTypes.size()))
            return comp.getErrorType();

        return *returnType;
    }

    ConstantValue eval(EvalContext&, const Args&,
                       const CallExpression::SystemCallInfo&) const final {
        return nullptr;
    }

    bool verifyConstant(EvalContext& context, const Args&, SourceRange range) const final {
        return notConst(context, range);
    }

private:
    std::vector<const Type*> argTypes;
    const Type* returnType;
    unsigned int nameOrHierIndex;
    size_t requiredArgs;
};

void registerCoverageFuncs(Compilation& c) {
#define REGISTER(name, ...) \
    c.addSystemSubroutine(std::make_unique<name>(__VA_ARGS__))
    REGISTER(CoverageNameOrHierFunc, "$coverage_control", c.getIntType(), 3, 4,
             std::vector{ &c.getIntType(), &c.getIntType(), &c.getIntType(), &c.getStringType() });
    REGISTER(CoverageNameOrHierFunc, "$coverage_get_max", c.getIntType(), 2, 3,
             std::vector{ &c.getIntType(), &c.getIntType(), &c.getStringType() });

    REGISTER(NonConstantFunction, "$coverage_get", c.getIntType(), 3,
             std::vector{ &c.getIntType(), &c.getIntType(), &c.getIntType() });
    REGISTER(NonConstantFunction, "$coverage_merge", c.getIntType(), 2,
             std::vector{ &c.getIntType(), &c.getStringType() });
    REGISTER(NonConstantFunction, "$coverage_save", c.getIntType(), 2,
             std::vector{ &c.getIntType(), &c.getStringType() });
    REGISTER(NonConstantFunction, "$get_coverage", c.getIntType());
    REGISTER(NonConstantFunction, "$set_coverage_db_name", c.getVoidType(), 1,
             std::vector{ &c.getStringType() });
    REGISTER(NonConstantFunction, "$load_coverage_db", c.getVoidType(), 1,
             std::vector{ &c.getStringType() });
#undef REGISTER
}

} // namespace slang::Builtins
