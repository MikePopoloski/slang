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
#include "DeclarationTable.h"
#include "Diagnostics.h"

namespace slang {

class SyntaxTree;
class Symbol;

/// SemanticModel is responsible for binding symbols and performing
/// type checking based on input parse trees.

class SemanticModel {
public:
    SemanticModel(DeclarationTable& declTable);

    void bindModuleImplicit(ModuleDeclarationSyntax* module);

private:
    Diagnostics diagnostics;
    BumpAllocator alloc;
    BufferPool<Symbol*> symbolPool;
};

}