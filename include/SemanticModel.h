//------------------------------------------------------------------------------
// SemanticModel.h
// Symbol binding and semantic analysis.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <deque>
#include <functional>
#include <memory>
#include <unordered_map>
#include <vector>

#include "AllSyntax.h"
#include "BoundNodes.h"
#include "BumpAllocator.h"
#include "DeclarationTable.h"
#include "Diagnostics.h"
#include "ExpressionBinder.h"
#include "HashMap.h"
#include "Scope.h"
#include "SmallVector.h"
#include "Symbol.h"

namespace slang {

class SyntaxTree;
class Symbol;

/// SemanticModel is responsible for binding symbols and performing
/// type checking based on input parse trees.
class SemanticModel {
public:
    SemanticModel(BumpAllocator& alloc, Diagnostics& diagnostics, DeclarationTable& declTable);

    InstanceSymbol* makeImplicitInstance(const ModuleDeclarationSyntax* syntax);
    InstanceSymbol* makeInstance(const ModuleDeclarationSyntax* decl, const ParameterValueAssignmentSyntax* parameterAssignments);

    const TypeSymbol* makeTypeSymbol(const DataTypeSyntax* syntax);

    /// Utilities for getting various common type symbols.
    const TypeSymbol* getErrorType() const { return getKnownType(SyntaxKind::Unknown); }
    const TypeSymbol* getKnownType(SyntaxKind kind) const;
    const TypeSymbol* getIntegralType(int width, bool isSigned, bool isFourState = true, bool isReg = false);

    // Generalized symbol lookup based on the current scope stack.
    const Symbol* lookupSymbol(StringRef name);

    BumpAllocator& getAllocator() { return alloc; }
    Diagnostics& getDiagnostics() { return diagnostics; }

private:
    struct ConstantRange {
        SVInt msb;
        SVInt lsb;
    };

    bool makeParameters(const ParameterDeclarationSyntax* syntax, SmallVector<ParameterSymbol*>& buffer,
                        HashMapBase<StringRef, SourceLocation>& nameDupMap,
                        bool lastLocal, bool overrideLocal, bool bodyParam);
    void evaluateParameter(ParameterSymbol* parameter);
    bool evaluateConstantDims(const SyntaxList<VariableDimensionSyntax>& dimensions, SmallVector<ConstantRange>& results);

    using ScopePtr = std::unique_ptr<Scope, std::function<void(Scope*)>>;
    ScopePtr pushScope();
    void popScope(const Scope* scope);

    template<typename TContainer>
    ScopePtr pushScope(const TContainer& range);

    BumpAllocator& alloc;
    Diagnostics& diagnostics;
    ExpressionBinder binder;
    DeclarationTable& declTable;
    std::deque<Scope> scopeStack;

    // preallocated type symbols for known types
    std::unordered_map<SyntaxKind, const TypeSymbol*> knownTypes;

    // cache of simple integral types keyed by {width, signedness, 4-state, isReg}
    std::unordered_map<uint64_t, const TypeSymbol*> integralTypeCache;
};

}