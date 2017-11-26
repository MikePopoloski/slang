//------------------------------------------------------------------------------
// SymbolFactory.h
// Symbol creation and caching.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "util/BumpAllocator.h"
#include "util/SmallVector.h"

#include "SymbolMap.h"
#include "TypeSymbols.h"

namespace slang {

/// A centralized location for creating and caching symbols. This includes
/// creating symbols from syntax nodes as well as fabricating them synthetically.
/// Common symbols such as built in types are exposed here as well.
class SymbolFactory : public BumpAllocator {
public:
    SymbolFactory();

    /// Creates symbols for the given syntax node.
    void createSymbols(const SyntaxNode& node, const Scope& parent, SmallVector<const Symbol*>& symbols);

    const CompilationUnitSymbol& createCompilationUnit(const SyntaxNode& node, const Scope& parent);

    const TypeSymbol& getType(SyntaxKind kind) const;
    const TypeSymbol& getType(const DataTypeSyntax& node, const Scope& parent);
    const IntegralTypeSymbol& getType(int width, bool isSigned, bool isFourState = true, bool isReg = false);
    const IntegralTypeSymbol& getType(int width, bool isSigned, bool isFourState, bool isReg, span<const int> lowerBounds, span<const int> widths);

    /// Various built-in type symbols for easy access.
    const IntegralTypeSymbol& getShortIntType() const { return shortIntType; }
    const IntegralTypeSymbol& getIntType() const { return intType; }
    const IntegralTypeSymbol& getLongIntType() const { return longIntType; }
    const IntegralTypeSymbol& getByteType() const { return byteType; }
    const IntegralTypeSymbol& getBitType() const { return bitType; }
    const IntegralTypeSymbol& getLogicType() const { return logicType; }
    const IntegralTypeSymbol& getRegType() const { return regType; }
    const IntegralTypeSymbol& getIntegerType() const { return integerType; }
    const IntegralTypeSymbol& getTimeType() const { return timeType; }
    const RealTypeSymbol& getRealType() const { return realType; }
    const RealTypeSymbol& getRealTimeType() const { return realTimeType; }
    const RealTypeSymbol& getShortRealType() const { return shortRealType; }
    const TypeSymbol& getstringType() const { return stringType; }
    const TypeSymbol& getCHandleType() const { return chandleType; }
    const TypeSymbol& getVoidType() const { return voidType; }
    const TypeSymbol& getEventType() const { return eventType; }
    const ErrorTypeSymbol& getErrorType() const { return errorType; }

    SymbolMap* createSymbolMap() { return symbolMapAllocator.emplace(); }

    ConstantValue* createConstant(ConstantValue&& value) { return constantAllocator.emplace(std::move(value)); }

    Symbol::LazyDefinition* createLazyDefinition(const Scope& scope, const HierarchyInstantiationSyntax& source) {
        return lazyDefinitionAllocator.emplace(&scope, &source);
    }

private:
    template<typename TNode>
    void createChildren(Scope* scope, const TNode& node);

    void createParamSymbols(const ParameterDeclarationSyntax& syntax, const Scope& parent,
                            SmallVector<const Symbol*>& symbols);

    TypedBumpAllocator<SymbolMap> symbolMapAllocator;
    TypedBumpAllocator<ConstantValue> constantAllocator;
    TypedBumpAllocator<Symbol::LazyDefinition> lazyDefinitionAllocator;

    std::unordered_map<SyntaxKind, const TypeSymbol*> knownTypes;
    std::unordered_map<uint64_t, const IntegralTypeSymbol*> integralTypeCache;

    IntegralTypeSymbol shortIntType;
    IntegralTypeSymbol intType;
    IntegralTypeSymbol longIntType;
    IntegralTypeSymbol byteType;
    IntegralTypeSymbol bitType;
    IntegralTypeSymbol logicType;
    IntegralTypeSymbol regType;
    IntegralTypeSymbol integerType;
    IntegralTypeSymbol timeType;
    RealTypeSymbol realType;
    RealTypeSymbol realTimeType;
    RealTypeSymbol shortRealType;
    TypeSymbol stringType;
    TypeSymbol chandleType;
    TypeSymbol voidType;
    TypeSymbol eventType;
    ErrorTypeSymbol errorType;
};

}