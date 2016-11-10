//------------------------------------------------------------------------------
// SemanticModel.h
// Symbol binding and semantic analysis.
//
// File is under the MIT license:
//------------------------------------------------------------------------------
#pragma once

#include <functional>
#include <memory>
#include <unordered_set>
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
    RealTime,
    // note: Error must always be the last value
    Error
};

/// SemanticModel is responsible for binding symbols and performing
/// type checking based on input parse trees.
class SemanticModel {
public:
    SemanticModel(BumpAllocator& alloc, Diagnostics& diagnostics);

	InstanceSymbol* makeImplicitInstance(const ModuleDeclarationSyntax* syntax);

	/// Utilities for getting various common type symbols.
    const TypeSymbol* getErrorType() const { return getSpecialType(SpecialType::Error); }
    const TypeSymbol* getSpecialType(SpecialType type) const { return specialTypes[(int)type]; }
    const TypeSymbol* getIntegralType(int width, bool isSigned);

	// Generalized symbol lookup based on the current scope stack.
	const Symbol* lookupSymbol(StringRef name);

	BumpAllocator& getAllocator() { return alloc; }

private:
	bool makeParameters(const ParameterPortDeclarationSyntax* syntax, Buffer<ParameterSymbol*>& buffer, bool lastLocal, bool overrideLocal);
	void evaluateParameter(ParameterSymbol* parameter);

	using ScopePtr = std::unique_ptr<Scope, std::function<void(Scope*)>>;
	ScopePtr pushScope();
	void popScope(const Scope* scope);

	template<typename TContainer>
	ScopePtr pushScope(const TContainer& range);

    BumpAllocator& alloc;
    Diagnostics& diagnostics;
	ExpressionBinder binder;
    BufferPool<Symbol*> symbolPool;
    std::unordered_set<StringRef> stringSet;
	std::vector<Scope> scopeStack;

    // preallocated type symbols for common types
    TypeSymbol* specialTypes[(int)SpecialType::Error+1];

	// cache of simple integral types; maps from width -> type, arrayed by 4-state/2-state and signed/unsigned
	std::unordered_map<int, const TypeSymbol*> integralTypeCache[2][2];
};

}