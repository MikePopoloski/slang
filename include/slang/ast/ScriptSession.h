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
    /// A bag of options to apply to the various evaluated snippets.
    Bag options;

    /// A compilation object that holds state across evaluation calls.
    Compilation compilation;

    /// A compilation unit that acts as a scope for evaluation.
    CompilationUnitSymbol& scope;

    /// Constructs a new ScriptSession.
    explicit ScriptSession(Bag options = {});

    /// Tries to evaluate the given snippet of SystemVerilog code
    /// and returns the result as a constant value.
    ConstantValue eval(std::string_view text);

    /// Tries to evaluate the given expression tree and returns the
    /// result as a constant value.
    ConstantValue evalExpression(const syntax::ExpressionSyntax& expr);

    /// Tries to evaluate the given statement tree and returns the
    /// result as a constant value.
    void evalStatement(const syntax::StatementSyntax& expr);

    /// Gets any diagnostics that have been issued during evaluation calls.
    Diagnostics getDiagnostics();

private:
    std::vector<std::shared_ptr<syntax::SyntaxTree>> syntaxTrees;
    ASTContext astCtx;
    EvalContext evalContext;
};

} // namespace slang::ast
