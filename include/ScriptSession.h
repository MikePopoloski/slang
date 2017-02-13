//------------------------------------------------------------------------------
// ScriptSession.h
// High-level interface to the compiler tools to evaluate snippets of code.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "ConstantEvaluator.h"
#include "SemanticModel.h"
#include "SyntaxTree.h"

namespace slang {

/// A helper class that allows evaluating arbitrary snippets of SystemVerilog
/// source code and maintaining state across multiple eval calls.
class ScriptSession {
public:
    ScriptSession() :
        declTable(diagnostics),
        sem(alloc, diagnostics, declTable),
        binder(sem, &scriptScope)
    {
    }

    ConstantValue eval(const std::string& text) {
        syntaxTrees.emplace_back(SyntaxTree::fromText(StringRef(text)));

        auto root = syntaxTrees.back().root();
        if (isExpression(root->kind))
            return evalExpression(root->as<ExpressionSyntax>());
        else if (isStatement(root->kind))
            return evalStatement(root->as<StatementSyntax>());
        else if (root->kind == SyntaxKind::DataDeclaration)
            return evalDeclaration(root->as<DataDeclarationSyntax>());
        else
            ASSERT(false, "Not supported yet");

        return nullptr;
    }

    ConstantValue evalExpression(const ExpressionSyntax* expr) {
        auto bound = binder.bindSelfDeterminedExpression(expr);
        return evaluator.evaluate(bound);
    }

    ConstantValue evalStatement(const StatementSyntax* stmt) {
        return nullptr;
    }

    ConstantValue evalDeclaration(const DataDeclarationSyntax* decl) {
        SmallVectorSized<const Symbol*, 8> results;
        sem.makeVariables(decl, results, &scriptScope);

        for (auto symbol : results) {
            auto& storage = evaluator.createTemporary(symbol);

            const auto& var = symbol->as<VariableSymbol>();
            if (var.initializer)
                storage = evaluator.evaluate(var.initializer);
            else
                storage = SVInt(0); // TODO: uninitialized variable
        }

        return nullptr;
    }

private:
    std::vector<SyntaxTree> syntaxTrees;
    Scope scriptScope;
    BumpAllocator alloc;
    Diagnostics diagnostics;
    DeclarationTable declTable;
    SemanticModel sem;
    ExpressionBinder binder;
    ConstantEvaluator evaluator;
};

}
