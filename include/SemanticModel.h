//------------------------------------------------------------------------------
// SemanticModel.h
// Symbol binding and semantic analysis.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <functional>
#include <memory>
#include <unordered_map>
#include <vector>

#include "AllSyntax.h"
#include "BoundNodes.h"
#include "Buffer.h"
#include "BufferPool.h"
#include "BumpAllocator.h"
#include "DeclarationTable.h"
#include "Diagnostics.h"
#include "ExpressionBinder.h"
#include "Scope.h"
#include "Symbol.h"

namespace slang {

class SyntaxTree;
class Symbol;

/// SemanticModel is responsible for binding symbols and performing
/// type checking based on input parse trees.
class SemanticModel {
public:
    SemanticModel(BumpAllocator& alloc, Diagnostics& diagnostics);

    InstanceSymbol* makeImplicitInstance(const ModuleDeclarationSyntax* syntax);

    const TypeSymbol* makeTypeSymbol(const DataTypeSyntax* syntax);

    /// Utilities for getting various common type symbols.
    const TypeSymbol* getErrorType() const { return getKnownType(SyntaxKind::Unknown); }
    const TypeSymbol* getKnownType(SyntaxKind kind) const;
    const TypeSymbol* getIntegralType(int width, bool isSigned, bool isFourState = true);

    // Generalized symbol lookup based on the current scope stack.
    const Symbol* lookupSymbol(StringRef name);

    BumpAllocator& getAllocator() { return alloc; }

private:
    struct ConstantRange {
        SVInt msb;
        SVInt lsb;
    };

    bool makeParameters(const ParameterDeclarationSyntax* syntax, Buffer<ParameterSymbol*>& buffer,
                        bool lastLocal, bool overrideLocal, bool bodyParam);
    void evaluateParameter(ParameterSymbol* parameter);
    bool evaluateConstantDims(const SyntaxList<VariableDimensionSyntax>& dimensions, Buffer<ConstantRange>& results);

    using ScopePtr = std::unique_ptr<Scope, std::function<void(Scope*)>>;
    ScopePtr pushScope();
    void popScope(const Scope* scope);

    template<typename TContainer>
    ScopePtr pushScope(const TContainer& range);

    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    ExpressionBinder binder;
    BufferPool<Symbol*> symbolPool;
    BufferPool<int> intPool;
    BufferPool<ConstantRange> constantRangePool;
    std::unordered_map<StringRef, SourceLocation> nameDupMap;
    std::vector<Scope> scopeStack;

    // preallocated type symbols for known types
    std::unordered_map<SyntaxKind, const TypeSymbol*> knownTypes;

    // cache of simple integral types; maps from width -> type, arrayed by 4-state/2-state and signed/unsigned
    std::unordered_map<int, const TypeSymbol*> integralTypeCache[2][2];
};

}