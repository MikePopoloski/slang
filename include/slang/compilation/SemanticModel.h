//------------------------------------------------------------------------------
// SemanticModel.h
// Query semantic information for a syntax tree.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>

#include "slang/symbols/HierarchySymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/TypeSymbols.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

class SemanticModel {
public:
    explicit SemanticModel(Compilation& compilation);

    const Symbol* getDeclaredSymbol(const SyntaxNode& syntax);

    const CompilationUnitSymbol* getDeclaredSymbol(const CompilationUnitSyntax& syntax);
    const InstanceSymbol* getDeclaredSymbol(const HierarchyInstantiationSyntax& syntax);
    const SequentialBlockSymbol* getDeclaredSymbol(const BlockStatementSyntax& syntax);
    const ProceduralBlockSymbol* getDeclaredSymbol(const ProceduralBlockSyntax& syntax);
    const GenerateBlockSymbol* getDeclaredSymbol(const IfGenerateSyntax& syntax);
    const GenerateBlockArraySymbol* getDeclaredSymbol(const LoopGenerateSyntax& syntax);
    const FormalArgumentSymbol* getDeclaredSymbol(const FunctionPortSyntax& syntax);
    const SubroutineSymbol* getDeclaredSymbol(const FunctionDeclarationSyntax& syntax);
    const EnumType* getDeclaredSymbol(const EnumTypeSyntax& syntax);
    const TypeAliasType* getDeclaredSymbol(const TypedefDeclarationSyntax& syntax);

private:
    Compilation& compilation;

    flat_hash_map<const SyntaxNode*, const Symbol*> symbolCache;
};

}