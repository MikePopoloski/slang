//------------------------------------------------------------------------------
// SemanticModel.h
// Symbol binding and semantic analysis.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include "AllSyntax.h"
#include "Buffer.h"
#include "BufferPool.h"
#include "BumpAllocator.h"
#include "Diagnostics.h"

namespace slang {

class SyntaxTree;
class Symbol;

/// SemanticModel is responsible for binding symbols and performing
/// type checking based on input parse trees.

class SemanticModel {
public:
    SemanticModel(ArrayRef<const SyntaxTree*> syntaxTrees);

private:
    void discoverHierarchy(const CompilationUnitSyntax* node);
    void discoverHierarchy(ModuleDeclarationSyntax* node);
    void discoverHierarchy(HierarchyInstantiationSyntax* node);
    void discoverHierarchy(FunctionDeclarationSyntax* node);
    void discoverHierarchy(GenerateRegionSyntax* node);
    void discoverHierarchy(LoopGenerateSyntax* node);
    void discoverHierarchy(CaseGenerateSyntax* node);
    void discoverHierarchy(IfGenerateSyntax* node);

    Diagnostics diagnostics;
    BumpAllocator alloc;
    ArrayRef<const SyntaxTree*> syntaxTrees;
    BufferPool<Symbol*> symbolPool;
};

}