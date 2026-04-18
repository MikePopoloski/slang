//------------------------------------------------------------------------------
// UserDefinedSubroutine.cpp
// User-defined system task and function support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/driver/UserDefinedSubroutine.h"

#include <fmt/format.h>

#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/parsing/Parser.h"
#include "slang/parsing/Preprocessor.h"
#include "slang/text/SourceManager.h"

namespace slang::driver {

using namespace ast;
using namespace parsing;
using namespace syntax;

nonstd::expected<std::shared_ptr<UserDefinedSubroutine>, std::string> UserDefinedSubroutine::create(
    std::string_view sv, SourceManager& sourceManager) {
    // Start by stripping whitespace.
    while (!sv.empty() && std::isspace((unsigned char)sv.front()))
        sv.remove_prefix(1);
    while (!sv.empty() && std::isspace((unsigned char)sv.back()))
        sv.remove_suffix(1);

    // Strip a trailing semicolon.
    if (!sv.empty() && sv.back() == ';')
        sv.remove_suffix(1);

    // Find the leading '$' that should start the name.
    const size_t dollarPos = sv.find('$');
    if (dollarPos == std::string_view::npos) {
        return nonstd::make_unexpected(
            fmt::format("'{}': subroutine name must start with '$'", sv));
    }

    // Massage the spec string into something the parser can accept.
    std::string str(sv);
    str[dollarPos] = ' ';

    // If there is anything prior to the name we will assume it's a task/function keyword.
    // Otherwise default to "task".
    if (dollarPos == 0)
        str = "task " + str;

    auto comp = std::make_unique<Compilation>();

    // Parse it.
    Diagnostics diagnostics;
    Preprocessor preprocessor(sourceManager, *comp, diagnostics);
    preprocessor.pushSource(sourceManager.assignText(str));

    Parser parser(preprocessor);
    auto& node = parser.parseFunctionPrototype();

    if (std::ranges::any_of(diagnostics, [](auto& d) { return d.isError(); }) || !parser.isDone()) {
        return nonstd::make_unexpected(
            fmt::format("'{}': failed to parse as a system task or function prototype", sv));
    }

    return std::shared_ptr<UserDefinedSubroutine>(new UserDefinedSubroutine(std::move(comp), node));
}

static std::string getName(const FunctionPrototypeSyntax& decl) {
    return "$" + std::string(decl.name->getLastToken().valueText());
}

static SubroutineKind getKind(const FunctionPrototypeSyntax& decl) {
    return decl.keyword.kind == TokenKind::TaskKeyword ? SubroutineKind::Task
                                                       : SubroutineKind::Function;
}

UserDefinedSubroutine::UserDefinedSubroutine(std::unique_ptr<ast::Compilation> compilation_,
                                             FunctionPrototypeSyntax& decl) :
    SystemSubroutine(getName(decl), getKind(decl)), compilation(std::move(compilation_)) {

    if (kind != SubroutineKind::Task || decl.portList) {
        // Wrap the prototype in a ClassMethodPrototypeSyntax with empty qualifiers
        // to reuse the existing fromSyntax machinery.
        SyntaxList<AttributeInstanceSyntax> emptyAttrs(nullptr);
        TokenList emptyQualifiers(nullptr);
        auto& classProto = *compilation->emplace<ClassMethodPrototypeSyntax>(emptyAttrs,
                                                                             emptyQualifiers, decl,
                                                                             Token{});

        proto = &MethodPrototypeSymbol::fromSyntax(compilation->getRootNoFinalize(), classProto);

        // Set the parent scope so that return-type resolution can find enclosing scopes.
        const_cast<MethodPrototypeSymbol*>(proto)->setParent(compilation->getRootNoFinalize());

        for (auto arg : proto->getArguments()) {
            if (arg->direction != ArgumentDirection::In &&
                (arg->direction != ArgumentDirection::Ref ||
                 !arg->flags.has(VariableFlags::Const))) {
                hasOutputArgs = true;
                break;
            }
        }
    }
}

UserDefinedSubroutine::~UserDefinedSubroutine() = default;

const Expression& UserDefinedSubroutine::bindArgument(size_t argIndex, const ASTContext& context,
                                                      const ExpressionSyntax& syntax,
                                                      const Args&) const {
    if (!proto)
        return Expression::bind(syntax, context);

    auto args = proto->getArguments();
    if (argIndex >= args.size())
        return Expression::bind(syntax, context);

    auto& arg = *args[argIndex];
    return Expression::bindArgument(arg.getType(), arg.direction, arg.flags, syntax, context);
}

const Type& UserDefinedSubroutine::checkArguments(const ASTContext& context, const Args& args,
                                                  SourceRange range, const Expression*) const {
    auto& comp = context.getCompilation();
    if (!proto)
        return comp.getVoidType();

    // Compute minimum and maximum argument counts.
    auto formalArgs = proto->getArguments();
    size_t maxArgs = formalArgs.size();
    size_t minArgs = 0;
    for (auto arg : formalArgs) {
        if (!arg->getDefaultValue())
            ++minArgs;
    }

    if (!checkArgCount(context, false, args, range, minArgs, maxArgs))
        return comp.getErrorType();

    return proto->getReturnType();
}

ConstantValue UserDefinedSubroutine::eval(EvalContext& context, const Args&, SourceRange range,
                                          const CallExpression::SystemCallInfo&) const {
    notConst(context, range);
    return nullptr;
}

} // namespace slang::driver
