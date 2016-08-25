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

class DeclarationTable {
public:
    explicit DeclarationTable(ArrayRef<const SyntaxTree*> syntaxTrees);

    SyntaxNode* find(StringRef

private:
    std::unordered_map<StringRef, SyntaxNode*> topLevel;
};

/// SemanticModel is responsible for binding symbols and performing
/// type checking based on input parse trees.

class SemanticModel {
public:
    SemanticModel() {}

    void discoverHierarchy(ArrayRef<const SyntaxTree*> syntaxTrees);

private:
    struct InitialHierarchyNode {
        StringRef name;
        SyntaxNode* syntax;
        ArrayRef<InitialHierarchyNode> children;

        InitialHierarchyNode(StringRef name, SyntaxNode* syntax) :
            name(name), syntax(syntax)
        {
        }
    };

    InitialHierarchyNode discoverHierarchy(HierarchyInstantiationSyntax* node, DeclarationTable& declTable);
    void discoverHierarchy(FunctionDeclarationSyntax* node);
    void discoverHierarchy(BlockStatementSyntax* node);
    void discoverHierarchy(DefParamSyntax* node);
    void discoverHierarchy(MemberSyntax* node);

    Diagnostics diagnostics;
    BumpAllocator alloc;
    BufferPool<Symbol*> symbolPool;
};

}