//------------------------------------------------------------------------------
// Compilation.h
// Central manager for compilation processes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "diagnostics/Diagnostics.h"
#include "symbols/TypeSymbols.h"
#include "util/BumpAllocator.h"
#include "util/SafeIndexedVector.h"
#include "util/SmallVector.h"

namespace slang {

/// A centralized location for creating and caching symbols. This includes
/// creating symbols from syntax nodes as well as fabricating them synthetically.
/// Common symbols such as built in types are exposed here as well.
class Compilation : public BumpAllocator {
public:
    Compilation();

    /// Adds a syntax tree to the compilation. Note that the syntax tree must outlive
    /// the compilation object. If the compilation has already been finalized by
    /// calling @a getRoot this call will throw an exception.
    void addSyntaxTree(const SyntaxTree& tree);

    /// Gets the root of the design. The first time you call this method all top-level
    /// instances will be elaborated and the compilation finalized. After that you can
    /// no longer make any modifications to the compilation object; any attempts to do
    /// so will result in an exception.
    const RootSymbol& getRoot();

    /// Indicates whether the design has been compiled and can no longer accept modifications.
    bool isFinalized() const { return finalized; }

    /// Gets the definition with the given name, or null if there is no such definition.
    const DefinitionSymbol* getDefinition(string_view name) const;

    /// Adds a definition to the map of global definitions.
    void addDefinition(const DefinitionSymbol& definition);

    /// Gets the package with the give name, or null if there is no such package.
    const PackageSymbol* getPackage(string_view name) const;

    /// Adds a package to the map of global packages.
    void addPackage(const PackageSymbol& package);

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
    const TypeSymbol& getStringType() const { return stringType; }
    const TypeSymbol& getCHandleType() const { return chandleType; }
    const TypeSymbol& getVoidType() const { return voidType; }
    const TypeSymbol& getEventType() const { return eventType; }
    const ErrorTypeSymbol& getErrorType() const { return errorType; }

    Diagnostics& diagnostics() { return diags; }
    const Diagnostics& diagnostics() const { return diags; }

    /// Report an error at the specified location.
    Diagnostic& addError(DiagCode code, SourceLocation location) {
        return diags.add(code, location);
    }

    SymbolMap* allocSymbolMap() { return symbolMapAllocator.emplace(); }

    ConstantValue* createConstant(ConstantValue&& value) { return constantAllocator.emplace(std::move(value)); }

    void addDeferredMembers(Scope::DeferredMemberIndex& index, const SyntaxNode& syntax);
    Scope::DeferredMemberData popDeferredMembers(Scope::DeferredMemberIndex index);

private:
    SubroutineSymbol& createSystemFunction(string_view name, SystemFunction kind,
                                           std::initializer_list<const TypeSymbol*> argTypes);

    // These functions are used for traversing the syntax hierarchy and finding all instantiations.
    using NameSet = flat_hash_set<string_view>;
    static void findInstantiations(const ModuleDeclarationSyntax& module,
                                   SmallVector<NameSet>& scopeStack, NameSet& found);
    static void findInstantiations(const MemberSyntax& node, SmallVector<NameSet>& scopeStack, NameSet& found);

    Diagnostics diags;
    RootSymbol root;
    bool finalized = false;

    // A set of names that are instantiated anywhere in the design. This is used to
    // determine which modules should be top-level instances (because nobody ever
    // instantiates them).
    NameSet instantiatedNames;

    // Specialized allocators for types that are not trivially destructible.
    TypedBumpAllocator<SymbolMap> symbolMapAllocator;
    TypedBumpAllocator<ConstantValue> constantAllocator;

    // Sideband data for scopes that have deferred members. This is mostly
    // a temporary state of affairs; once a scope expands its members it
    // will pop its storage here.
    SafeIndexedVector<Scope::DeferredMemberData, Scope::DeferredMemberIndex> deferredData;

    // The name map for global definitions.
    flat_hash_map<string_view, const DefinitionSymbol*> definitionMap;

    // The name map for packages. Note that packages have their own namespace,
    // which is why they can't share the definitions name table.
    flat_hash_map<string_view, const PackageSymbol*> packageMap;

    // A cache of integral types, keyed on various properties such as width.
    flat_hash_map<uint64_t, const IntegralTypeSymbol*> integralTypeCache;

    // Map from syntax kinds to the built-in types.
    flat_hash_map<SyntaxKind, const TypeSymbol*> knownTypes;

    // Instances of all the built-in types.
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