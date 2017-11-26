//------------------------------------------------------------------------------
// ScriptSession.h
// High-level interface to the compiler tools to evaluate snippets of code.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "analysis/Binder.h"
#include "analysis/RootSymbol.h"
#include "parsing/SyntaxTree.h"

namespace slang {

/// A helper class that allows evaluating arbitrary snippets of SystemVerilog
/// source code and maintaining state across multiple eval calls.
class ScriptSession {
public:
    ScriptSession() : scope(root) {}

    ConstantValue eval(const std::string& text) {
        syntaxTrees.emplace_back(SyntaxTree::fromText(string_view(text)));

        const auto& node = syntaxTrees.back().root();
        switch (node.kind) {
            case SyntaxKind::ParameterDeclarationStatement:
            case SyntaxKind::FunctionDeclaration:
            case SyntaxKind::TaskDeclaration:
            case SyntaxKind::InterfaceDeclaration:
            case SyntaxKind::ModuleDeclaration:
            case SyntaxKind::HierarchyInstantiation:
                scope.createAndAddSymbols(syntaxTrees.back().root());
                return nullptr;
            case SyntaxKind::DataDeclaration: {
                for (auto symbol : scope.createAndAddSymbols(syntaxTrees.back().root())) {
                    ConstantValue initial;
                    const auto& variable = symbol->as<VariableSymbol>();
                    if (variable.initializer)
                        initial = variable.initializer->eval(evalContext);
                    else
                        initial = { *variable.type, SVInt(0) };

                    evalContext.createLocal(symbol, initial);
                }
                return nullptr;
            }
            default:
                if (isExpression(node.kind))
                    return evalExpression(node.as<ExpressionSyntax>());
                else if (isStatement(node.kind))
                    return evalStatement(node.as<StatementSyntax>());
                else
                    // TODO: not supported yet
                    THROW_UNREACHABLE;
        }
    }

    ConstantValue evalExpression(const ExpressionSyntax& expr) {
        const auto& bound = Binder(scope, LookupKind::Direct).bindConstantExpression(expr);
        return bound.eval(evalContext);
    }

    ConstantValue evalStatement(const StatementSyntax&) {
        // TODO:
        return nullptr;
    }

    std::string reportDiagnostics() {
        if (syntaxTrees.empty())
            return "";

        return DiagnosticWriter(syntaxTrees[0].sourceManager()).report(diagnostics);
    }

private:
    std::vector<SyntaxTree> syntaxTrees;
    BumpAllocator alloc;
    Diagnostics diagnostics;
    RootSymbol root;
    DynamicScopeSymbol scope;
    EvalContext evalContext;
};

}
