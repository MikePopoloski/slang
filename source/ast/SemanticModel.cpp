//------------------------------------------------------------------------------
// SemanticModel.cpp
// Query semantic information for a syntax tree
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/SemanticModel.h"

#include "slang/ast/Compilation.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;

SemanticModel::SemanticModel(Compilation& compilation) : compilation(compilation) {
}

void SemanticModel::withContext(const SyntaxNode& node, const Symbol& symbol) {
    symbolCache[&node] = &symbol;
}

const Symbol* SemanticModel::getDeclaredSymbol(const SyntaxNode& syntax) {
    // If we've already cached this node, return that.
    if (auto it = symbolCache.find(&syntax); it != symbolCache.end())
        return it->second;

    // If we hit the top of the syntax tree, look in the compilation for the correct symbol.
    if (syntax.kind == SyntaxKind::CompilationUnit) {
        auto result = compilation.getCompilationUnit(syntax.as<CompilationUnitSyntax>());
        if (result)
            symbolCache[&syntax] = result;
        return result;
    }
    else if (syntax.kind == SyntaxKind::ModuleDeclaration ||
             syntax.kind == SyntaxKind::InterfaceDeclaration ||
             syntax.kind == SyntaxKind::ProgramDeclaration) {
        auto def = compilation.getDefinition(syntax.as<ModuleDeclarationSyntax>());
        if (!def)
            return nullptr;

        // There is no symbol to use here so create a placeholder instance.
        auto result = &InstanceSymbol::createDefault(compilation, *def, nullptr);
        symbolCache[&syntax] = result;
        return result;
    }

    // Otherwise try to find the parent symbol first.
    auto parent = syntax.parent ? getDeclaredSymbol(*syntax.parent) : nullptr;
    if (!parent)
        return nullptr;

    // If this is a type alias, unwrap its target type to look at the syntax node.
    if (parent->kind == SymbolKind::TypeAlias) {
        auto& target = parent->as<TypeAliasType>().targetType.getType();
        if (target.getSyntax() == &syntax) {
            symbolCache.emplace(&syntax, &target);
            return &target;
        }
        return nullptr;
    }

    if (parent->kind == SymbolKind::Instance)
        parent = &parent->as<InstanceSymbol>().body;
    else if (!parent->isScope())
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

const StatementBlockSymbol* SemanticModel::getDeclaredSymbol(const BlockStatementSyntax& syntax) {
    auto result = getDeclaredSymbol((const SyntaxNode&)syntax);
    return result ? &result->as<StatementBlockSymbol>() : nullptr;
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

} // namespace slang::ast
