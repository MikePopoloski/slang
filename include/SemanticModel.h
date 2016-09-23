//------------------------------------------------------------------------------
// SemanticModel.h
// Symbol binding and semantic analysis.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include "AllSyntax.h"
#include "BoundNodes.h"
#include "Buffer.h"
#include "BufferPool.h"
#include "BumpAllocator.h"
#include "DeclarationTable.h"
#include "Diagnostics.h"

namespace slang {

class SyntaxTree;
class Symbol;

enum class SpecialType {
    ShortInt,
    Int,
    LongInt,
    Byte,
    Bit,
    Logic,
    Reg,
    Integer,
    Time,
    Real,
    ShortReal,
    RealTime
    // note: if you update this enum you have to update
    // the table of special types in SemanticModel
};

enum class ValueCategory {
    None,
    Constant
};

/// SemanticModel is responsible for binding symbols and performing
/// type checking based on input parse trees.
class SemanticModel {
public:
    SemanticModel();
    SemanticModel(DeclarationTable& declTable);

    void bindModuleImplicit(ModuleDeclarationSyntax* module);
    BoundParameterDeclaration* bindParameterDecl(const ParameterDeclarationSyntax* syntax);
    BoundExpression* bindExpression(ExpressionSyntax* syntax);
    BoundExpression* bindLiteral(const LiteralExpressionSyntax* syntax);

    const TypeSymbol* getSpecialType(SpecialType type) const;
    void foldConstants(BoundExpression* expression);

private:
    Diagnostics diagnostics;
    BumpAllocator alloc;
    BufferPool<Symbol*> symbolPool;

    // preallocated type symbols for common types
    TypeSymbol* specialTypes[(int)SpecialType::RealTime];
};

}