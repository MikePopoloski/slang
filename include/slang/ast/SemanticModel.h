//------------------------------------------------------------------------------
//! @file SemanticModel.h
//! @brief Query semantic information for a syntax tree
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Hash.h"

namespace slang::ast {

class SLANG_EXPORT SemanticModel {
public:
    explicit SemanticModel(Compilation& compilation);

    void withContext(const syntax::SyntaxNode& node, const Symbol& symbol);

    const Symbol* getDeclaredSymbol(const syntax::SyntaxNode& syntax);

    const CompilationUnitSymbol* getDeclaredSymbol(const syntax::CompilationUnitSyntax& syntax);
    const InstanceSymbol* getDeclaredSymbol(const syntax::HierarchyInstantiationSyntax& syntax);
    const StatementBlockSymbol* getDeclaredSymbol(const syntax::BlockStatementSyntax& syntax);
    const ProceduralBlockSymbol* getDeclaredSymbol(const syntax::ProceduralBlockSyntax& syntax);
    const GenerateBlockSymbol* getDeclaredSymbol(const syntax::IfGenerateSyntax& syntax);
    const GenerateBlockArraySymbol* getDeclaredSymbol(const syntax::LoopGenerateSyntax& syntax);
    const SubroutineSymbol* getDeclaredSymbol(const syntax::FunctionDeclarationSyntax& syntax);
    const EnumType* getDeclaredSymbol(const syntax::EnumTypeSyntax& syntax);
    const TypeAliasType* getDeclaredSymbol(const syntax::TypedefDeclarationSyntax& syntax);

private:
    Compilation& compilation;

    flat_hash_map<const syntax::SyntaxNode*, const Symbol*> symbolCache;
};

} // namespace slang::ast
