//------------------------------------------------------------------------------
// SemanticModel.h
// Symbol binding and semantic analysis.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <unordered_map>

#include "AllSyntax.h"
#include "Buffer.h"
#include "BufferPool.h"
#include "BumpAllocator.h"
#include "Diagnostics.h"

namespace slang {

class SyntaxTree;
class Symbol;

/// The DeclarationTable keeps track of top-level modules for future lookup.
/// It also tacks the location of all defparams in the design, which are the
/// only other constructs that can refer to items in other compilation units.
class DeclarationTable {
public:
    void addSyntaxTree(const SyntaxTree* tree);

    SyntaxNode* find(StringRef name);

private:
    std::unordered_map<StringRef, SyntaxNode*> nodes;
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

        InitialHierarchyNode(std::nullptr_t) : syntax(nullptr) {}
        InitialHierarchyNode(StringRef name, SyntaxNode* syntax) :
            name(name), syntax(syntax)
        {
        }
    };

    void discoverHierarchy(HierarchyInstantiationSyntax* node, DeclarationTable& declTable, Buffer<InitialHierarchyNode>& buffer);
    void discoverHierarchy(FunctionDeclarationSyntax* node);
    void discoverHierarchy(BlockStatementSyntax* node);
    void discoverHierarchy(DefParamSyntax* node);
    void discoverHierarchy(MemberSyntax* node);

    Diagnostics diagnostics;
    BumpAllocator alloc;
    BufferPool<Symbol*> symbolPool;
};

}