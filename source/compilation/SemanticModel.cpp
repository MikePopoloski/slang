//------------------------------------------------------------------------------
// SemanticModel.cpp
// Query semantic information for a syntax tree.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/compilation/SemanticModel.h"

#include "slang/compilation/Compilation.h"

namespace slang {

SemanticModel::SemanticModel(Compilation& compilation) :
    compilation(compilation) {}

const Symbol* SemanticModel::getDeclaredSymbol(const SyntaxNode& syntax) {
    // If we've already cached this node, return that.
    if (auto it = symbolCache.find(&syntax); it != symbolCache.end())
        return it->second;

    // If we hit the top of the syntax tree, look in the compilation for the correct symbol.
    if (syntax.kind == SyntaxKind::CompilationUnit) {
        auto result = compilation.getCompilationUnit(syntax.as<CompilationUnitSyntax>());
        if (result)
            symbolCache.emplace(&syntax, result);
        return result;
    }

    // Otherwise try to find the parent symbol first.
    auto parent = syntax.parent ? getDeclaredSymbol(*syntax.parent) : nullptr;
    if (!parent || !parent->isScope())
        return nullptr;

    // Search among the parent's children to see if we can find ourself.
    for (auto& child : parent->as<Scope>().members()) {
        if (child.getSyntax() == &syntax) {
            // We found ourselves, hurray.
            symbolCache.emplace(&syntax, &child);
            return &child;
        }
    }
    return nullptr;
}

const CompilationUnitSymbol* SemanticModel::getDeclaredSymbol(const CompilationUnitSyntax& syntax) {
    auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
    return result ? &result->as<CompilationUnitSymbol>() : nullptr;
}

const InstanceSymbol* SemanticModel::getDeclaredSymbol(const HierarchyInstantiationSyntax& syntax) {
    auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
    return result ? &result->as<InstanceSymbol>() : nullptr;
}

const SequentialBlockSymbol* SemanticModel::getDeclaredSymbol(const BlockStatementSyntax& syntax) {
    auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
    return result ? &result->as<SequentialBlockSymbol>() : nullptr;
}

const ProceduralBlockSymbol* SemanticModel::getDeclaredSymbol(const ProceduralBlockSyntax& syntax) {
    auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
    return result ? &result->as<ProceduralBlockSymbol>() : nullptr;
}

const GenerateBlockSymbol* SemanticModel::getDeclaredSymbol(const IfGenerateSyntax& syntax) {
    auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
    return result ? &result->as<GenerateBlockSymbol>() : nullptr;
}

const GenerateBlockArraySymbol* SemanticModel::getDeclaredSymbol(const LoopGenerateSyntax& syntax) {
    auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
    return result ? &result->as<GenerateBlockArraySymbol>() : nullptr;
}

const FormalArgumentSymbol* SemanticModel::getDeclaredSymbol(const FunctionPortSyntax& syntax) {
    auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
    return result ? &result->as<FormalArgumentSymbol>() : nullptr;
}

const SubroutineSymbol* SemanticModel::getDeclaredSymbol(const FunctionDeclarationSyntax& syntax) {
    auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
    return result ? &result->as<SubroutineSymbol>() : nullptr;
}

const EnumType* SemanticModel::getDeclaredSymbol(const EnumTypeSyntax& syntax) {
    auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
    return result ? &result->as<EnumType>() : nullptr;
}

const TypeAliasType* SemanticModel::getDeclaredSymbol(const TypedefDeclarationSyntax& syntax) {
    auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
    return result ? &result->as<TypeAliasType>() : nullptr;
}

}