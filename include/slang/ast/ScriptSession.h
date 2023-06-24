//------------------------------------------------------------------------------
//! @file ScriptSession.h
//! @brief High-level interface to the compiler tools to evaluate snippets of code
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::syntax {
class SyntaxTree;
}

namespace slang::ast {

/// A helper class that allows evaluating arbitrary snippets of SystemVerilog
/// source code and maintaining state across multiple eval calls.
class SLANG_EXPORT ScriptSession {
public:
    Compilation compilation;
    CompilationUnitSymbol& scope;

    ScriptSession();

    ConstantValue eval(std::string_view text);
    ConstantValue evalExpression(const syntax::ExpressionSyntax& expr);
    void evalStatement(const syntax::StatementSyntax& expr);

    Diagnostics getDiagnostics();

private:
    std::vector<std::shared_ptr<syntax::SyntaxTree>> syntaxTrees;
    EvalContext evalContext;
};

} // namespace slang::ast
