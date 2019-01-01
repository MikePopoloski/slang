//------------------------------------------------------------------------------
// ScriptSession.h
// High-level interface to the compiler tools to evaluate snippets of code.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "slang/compilation/Compilation.h"
#include "slang/syntax/SyntaxTree.h"

namespace slang {

/// A helper class that allows evaluating arbitrary snippets of SystemVerilog
/// source code and maintaining state across multiple eval calls.
class ScriptSession {
public:
    ScriptSession();

    ConstantValue eval(string_view text);
    ConstantValue evalExpression(const ExpressionSyntax& expr);

    Diagnostics getDiagnostics();

private:
    std::vector<std::shared_ptr<SyntaxTree>> syntaxTrees;
    Compilation compilation;
    CompilationUnitSymbol& scope;
    EvalContext evalContext;
};

} // namespace slang
