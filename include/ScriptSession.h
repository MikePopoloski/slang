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

#include <tuple>

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

    void addToSyntaxTrees(const std::string &text) {
        syntaxTrees.emplace_back(SyntaxTree::fromText(StringRef(text)));
    }

    SyntaxTree &lastSyntaxTree() {
        return syntaxTrees.back();
    }

    ConstantValue evalLastSyntaxTree() {
        auto root = lastSyntaxTree().root();
        switch (root->kind) {
            case SyntaxKind::ParameterDeclarationStatement:
                return evalParameterDeclaration(root->as<ParameterDeclarationStatementSyntax>());
            case SyntaxKind::DataDeclaration:
                return evalVariableDeclaration(root->as<DataDeclarationSyntax>());
            case SyntaxKind::FunctionDeclaration:
            case SyntaxKind::TaskDeclaration:
                return evalSubroutineDeclaration(root->as<FunctionDeclarationSyntax>());
            case SyntaxKind::InterfaceDeclaration:
            case SyntaxKind::ModuleDeclaration: {
                auto module = root->as<ModuleDeclarationSyntax>();
                declTable.addMember(module);
                // construct a blank module with empty scope linking to this scope
                auto scope = alloc.emplace<Scope>();
                scope->addParentScope(&scriptScope);
                auto moduleSym = alloc.emplace<ModuleSymbol>(module, scope, ArrayRef<const Symbol*>());
                scriptScope.add(moduleSym);
                return true;
            }
            case SyntaxKind::HierarchyInstantiation: {
                SmallVectorSized<const Symbol*, 8> results;
                sem.handleInstantiation(root->as<HierarchyInstantiationSyntax>(), results, &scriptScope);
                return true;
            }
            case SyntaxKind::IdentifierName:
            case SyntaxKind::ScopedName: {
                auto expr = binder.bindConstantExpression(root->as<NameSyntax>());
                ASSERT(!expr->bad());
                return sem.evaluateConstant(expr);
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

    ConstantValue eval(const std::string& text) {
        addToSyntaxTrees(text);
        return evalLastSyntaxTree();
    }

    const char* lastSyntaxTreeKind() {
        SyntaxKind kind = lastSyntaxTree().root()->kind;
        switch (kind) {
            case SyntaxKind::DataDeclaration: return "Variable declaration";
            case SyntaxKind::FunctionDeclaration: return "Function";
            case SyntaxKind::TaskDeclaration: return "Task";
            case SyntaxKind::InterfaceDeclaration: return "Interface";
            case SyntaxKind::ModuleDeclaration: return "Module";
            case SyntaxKind::HierarchyInstantiation: return "Hierarchy instantiation";
            default:
                if (isExpression(kind)) return "Expression";
                else if (isStatement(kind)) return "Statement";
                else return "Unknown, possibly a duck";
        }
    }

    ConstantValue evalExpression(const ExpressionSyntax* expr) {
        auto bound = binder.bindSelfDeterminedExpression(expr);
        return evaluator.evaluateExpr(bound);
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
                storage = evaluator.evaluateExpr(var.initializer);
            else
                storage = SVInt(0); // TODO: uninitialized variable
        }
        // TODO: add to scope?
        return nullptr;
    }

    ConstantValue evalParameterDeclaration(const ParameterDeclarationStatementSyntax* decl) {
        for (auto paramDecl : decl->parameter->declarators) {
            auto paramSym = alloc.emplace<ParameterSymbol>(
                paramDecl->name.valueText(), paramDecl->name.location(), decl->parameter, paramDecl,
                decl->parameter->keyword.kind == TokenKind::LocalParamKeyword);
            sem.evaluateParameter(paramSym, paramDecl->initializer->expr, &scriptScope);
            scriptScope.add(paramSym);
        }
        return nullptr;
    }

    ConstantValue evalSubroutineDeclaration(const FunctionDeclarationSyntax* decl) {
        auto symbol = sem.makeSubroutine(decl, &scriptScope);
        scriptScope.add(symbol);
        return nullptr;
    }

    Diagnostics &getDiagnostics() { return diagnostics; }

    std::string reportDiagnostics() {
        return DiagnosticWriter(SyntaxTree::getDefaultSourceManager()).report(diagnostics);
    }

    std::string dumpScope() {
        return scriptScope.toString();
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
