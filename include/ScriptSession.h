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
        scriptScope(sem.getSystemScope()),
        binder(sem, &scriptScope)
    {
    }

    ConstantValue eval(const std::string& text) {
        syntaxTrees.emplace_back(SyntaxTree::fromText(StringRef(text)));

        auto root = syntaxTrees.back().root();
        switch (root->kind) {
            case SyntaxKind::DataDeclaration:
                return evalVariableDeclaration(root->as<DataDeclarationSyntax>());
            case SyntaxKind::FunctionDeclaration:
            case SyntaxKind::TaskDeclaration:
                return evalSubroutineDeclaration(root->as<FunctionDeclarationSyntax>());
            case SyntaxKind::ModuleDeclaration: {
                auto module = root->as<ModuleDeclarationSyntax>();
                auto inst = sem.makeImplicitInstance(module);
                return scriptScope.add(inst);
            }
            default:
                if (isExpression(root->kind))
                    return evalExpression(root->as<ExpressionSyntax>());
                else if (isStatement(root->kind))
                    return evalStatement(root->as<StatementSyntax>());
                else
                    ASSERT(false, "Not supported yet");
        }
        return nullptr;
    }

    ConstantValue evalExpression(const ExpressionSyntax* expr) {
        auto bound = binder.bindSelfDeterminedExpression(expr);
        return evaluator.evaluate(bound);
    }

    ConstantValue evalStatement(const StatementSyntax* stmt) {
        return nullptr;
    }

    ConstantValue evalVariableDeclaration(const DataDeclarationSyntax* decl) {
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

    ConstantValue evalSubroutineDeclaration(const FunctionDeclarationSyntax* decl) {
        auto symbol = sem.makeSubroutine(decl, &scriptScope);
        scriptScope.add(symbol);
        return nullptr;
    }

    std::string reportDiagnostics() {
        return DiagnosticWriter(SyntaxTree::getDefaultSourceManager()).report(diagnostics);
    }

private:
    std::vector<SyntaxTree> syntaxTrees;
    BumpAllocator alloc;
    Diagnostics diagnostics;
    DeclarationTable declTable;
    SemanticModel sem;
    Scope scriptScope;
    ExpressionBinder binder;
    ConstantEvaluator evaluator;
};

}
