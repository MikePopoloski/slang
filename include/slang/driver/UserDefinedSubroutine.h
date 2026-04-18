//------------------------------------------------------------------------------
//! @file UserDefinedSubroutine.h
//! @brief User-defined system task and function support
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <expected.hpp>
#include <memory>
#include <string>

#include "slang/ast/SystemSubroutine.h"
#include "slang/util/BumpAllocator.h"

namespace slang {
class SourceManager;
}

namespace slang::ast {

class Compilation;
class MethodPrototypeSymbol;

} // namespace slang::ast

namespace slang::syntax {
struct FunctionPrototypeSyntax;
}

namespace slang::driver {

class SLANG_EXPORT UserDefinedSubroutine : public ast::SystemSubroutine {
public:
    static nonstd::expected<std::shared_ptr<UserDefinedSubroutine>, std::string> create(
        std::string_view spec, SourceManager& sourceManager);

    ~UserDefinedSubroutine();

    const ast::Expression& bindArgument(size_t argIndex, const ast::ASTContext& context,
                                        const syntax::ExpressionSyntax& syntax,
                                        const Args& previousArgs) const final;

    const ast::Type& checkArguments(const ast::ASTContext& context, const Args& args,
                                    SourceRange range, const ast::Expression*) const final;

    ConstantValue eval(ast::EvalContext& context, const Args&, SourceRange range,
                       const ast::CallExpression::SystemCallInfo&) const final;

private:
    UserDefinedSubroutine(std::unique_ptr<ast::Compilation> compilation,
                          syntax::FunctionPrototypeSyntax& decl);

    std::unique_ptr<ast::Compilation> compilation;
    const ast::MethodPrototypeSymbol* proto = nullptr;
};

} // namespace slang::driver
