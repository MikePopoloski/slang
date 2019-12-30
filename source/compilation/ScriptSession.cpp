//------------------------------------------------------------------------------
// ScriptSession.cpp
// High-level interface to the compiler tools to evaluate snippets of code.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/compilation/ScriptSession.h"

#include "slang/binding/Expression.h"
#include "slang/symbols/CompilationUnitSymbols.h"
#include "slang/symbols/VariableSymbols.h"

namespace slang {

ScriptSession::ScriptSession() :
    scope(compilation.createScriptScope()), evalContext(scope, EvalFlags::IsScript) {
}

ConstantValue ScriptSession::eval(string_view text) {
    syntaxTrees.emplace_back(SyntaxTree::fromText(text, "source"));

    const auto& node = syntaxTrees.back()->root();
    switch (node.kind) {
        case SyntaxKind::ParameterDeclarationStatement:
        case SyntaxKind::FunctionDeclaration:
        case SyntaxKind::TaskDeclaration:
        case SyntaxKind::InterfaceDeclaration:
        case SyntaxKind::ModuleDeclaration:
        case SyntaxKind::HierarchyInstantiation:
        case SyntaxKind::TypedefDeclaration:
            scope.addMembers(node);
            return nullptr;
        case SyntaxKind::DataDeclaration: {
            SmallVectorSized<const ValueSymbol*, 2> symbols;
            VariableSymbol::fromSyntax(compilation, node.as<DataDeclarationSyntax>(), scope,
                                       symbols);

            for (auto symbol : symbols) {
                scope.addMember(*symbol);

                ConstantValue initial;
                if (auto initializer = symbol->getInitializer())
                    initial = initializer->eval(evalContext);

                evalContext.createLocal(symbol, initial);
            }
            return nullptr;
        }
        default:
            if (ExpressionSyntax::isKind(node.kind))
                return evalExpression(node.as<ExpressionSyntax>());
            else
                // If this throws, ScriptSession doesn't currently support whatever construct
                // you were trying to evaluate. Add support to the case above.
                THROW_UNREACHABLE;
    }
}

ConstantValue ScriptSession::evalExpression(const ExpressionSyntax& expr) {
    BindContext context(scope, LookupLocation::max, BindFlags::ProceduralStatement);
    auto& bound = Expression::bind(expr, context, BindFlags::AssignmentAllowed);
    return bound.eval(evalContext);
}

Diagnostics ScriptSession::getDiagnostics() {
    Diagnostics result;
    for (auto& tree : syntaxTrees)
        result.appendRange(tree->diagnostics());

    result.appendRange(compilation.getAllDiagnostics());
    result.appendRange(evalContext.getDiagnostics());
    return result;
}

} // namespace slang