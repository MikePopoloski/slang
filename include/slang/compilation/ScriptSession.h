//------------------------------------------------------------------------------
//! @file ScriptSession.h
//! @brief High-level interface to the compiler tools to evaluate snippets of code
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/EvalContext.h"
#include "slang/compilation/Compilation.h"
#include "slang/syntax/SyntaxTree.h"

namespace slang {

struct ExpressionSyntax;
struct StatementSyntax;

/// A helper class that allows evaluating arbitrary snippets of SystemVerilog
/// source code and maintaining state across multiple eval calls.
class ScriptSession {
public:
    Compilation compilation;
    CompilationUnitSymbol& scope;

    ScriptSession();

    ConstantValue eval(string_view text);
    ConstantValue evalExpression(const ExpressionSyntax& expr);
    void evalStatement(const StatementSyntax& expr);

    Diagnostics getDiagnostics();

private:
    std::vector<std::shared_ptr<SyntaxTree>> syntaxTrees;
    EvalContext evalContext;
};

} // namespace slang
