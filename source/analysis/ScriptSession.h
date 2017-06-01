//------------------------------------------------------------------------------
// ScriptSession.h
// High-level interface to the compiler tools to evaluate snippets of code.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "analysis/Binder.h"
#include "parsing/SyntaxTree.h"
#include "ConstantEvaluator.h"
#include "SemanticModel.h"

namespace slang {

/// A helper class that allows evaluating arbitrary snippets of SystemVerilog
/// source code and maintaining state across multiple eval calls.
class ScriptSession {
public:
    ConstantValue eval(const std::string& text) {
        syntaxTrees.emplace_back(SyntaxTree::fromText(StringRef(text)));

        const auto& node = syntaxTrees.back().root();
        switch (node.kind) {
            case SyntaxKind::ParameterDeclarationStatement:
            case SyntaxKind::FunctionDeclaration:
            case SyntaxKind::TaskDeclaration:
            case SyntaxKind::InterfaceDeclaration:
            case SyntaxKind::ModuleDeclaration:
            case SyntaxKind::HierarchyInstantiation:
                root.addTree(syntaxTrees.back());
                return true;

            case SyntaxKind::DataDeclaration: {
                SmallVectorSized<const Symbol*, 4> results;
                root.createMembers(syntaxTrees.back().root(), results);
                for (auto symbol : results) {
                    ConstantValue& cv = evaluator.createTemporary(*symbol);

                    const BoundExpression* init = symbol->as<VariableSymbol>().initializer();
                    if (init)
                        cv = evaluator.evaluateExpr(*init);
                    else
                        cv = SVInt(0);
                }
				return true;
            }

            default:
                if (isExpression(node.kind))
                    return evalExpression(node.as<ExpressionSyntax>());
                else if (isStatement(node.kind))
                    return evalStatement(node.as<StatementSyntax>());
                else
                    ASSERT(false, "Not supported yet");
        }
        return nullptr;
    }

    ConstantValue evalExpression(const ExpressionSyntax& expr) {
        const auto& bound = Binder(root).bindConstantExpression(expr);
        if (bound.bad())
            return nullptr;

        return evaluator.evaluateExpr(bound);
    }

    ConstantValue evalStatement(const StatementSyntax& stmt) {
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
	DesignRootSymbol root;
    ConstantEvaluator evaluator;
};

}
