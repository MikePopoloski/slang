//------------------------------------------------------------------------------
// Compilation.h
// Central manager for compilation processes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <memory>

#include "binding/Expressions.h"
#include "diagnostics/Diagnostics.h"
#include "symbols/HierarchySymbols.h"
#include "symbols/TypeSymbols.h"
#include "util/BumpAllocator.h"
#include "util/SafeIndexedVector.h"
#include "util/SmallVector.h"

namespace slang {

class SyntaxTree;

/// A centralized location for creating and caching symbols. This includes
/// creating symbols from syntax nodes as well as fabricating them synthetically.
/// Common symbols such as built in types are exposed here as well.
class Compilation : public BumpAllocator {
public:
    Compilation();

    /// Adds a syntax tree to the compilation. If the compilation has already been finalized
    /// by calling @a getRoot this call will throw an exception.
    void addSyntaxTree(std::shared_ptr<SyntaxTree> tree);

    /// Gets the root of the design. The first time you call this method all top-level
    /// instances will be elaborated and the compilation finalized. After that you can
    /// no longer make any modifications to the compilation object; any attempts to do
    /// so will result in an exception.
    const RootSymbol& getRoot();

    /// Indicates whether the design has been compiled and can no longer accept modifications.
    bool isFinalized() const { return finalized; }

    /// Gets the definition with the given name, or null if there is no such definition.
    /// This takes into account the given scope so that nested definitions are found before more global ones.
    const Definition* getDefinition(string_view name, const Scope& scope) const;

    /// Adds a definition to the set of definitions tracked in the compilation.
    void addDefinition(const ModuleDeclarationSyntax& syntax, const Scope& scope);

    /// Gets the package with the give name, or null if there is no such package.
    const PackageSymbol* getPackage(string_view name) const;

    /// Adds a package to the map of global packages.
    void addPackage(const PackageSymbol& package);

    /// A convenience method for parsing a name string and turning it into a set of syntax nodes.
    /// This is mostly for testing and API purposes; normal compilation never does this.
    const NameSyntax& parseName(string_view name);

    /// Creates a new compilation unit within the design that can be modified dynamically,
    /// which is useful in runtime scripting scenarios. Note that this call will succeed
    /// even if the design has been finalized, but in that case any instantiations in the
    /// script scope won't affect which modules are determined to be top-level instances.
    CompilationUnitSymbol& createScriptScope();

    /// Gets the source manager associated with the compilation. If no syntax trees have
    /// been added to the design this method will return null.
    const SourceManager* getSourceManager() const { return sourceManager; }

    /// Gets the diagnostics produced during lexing, preprocessing, and syntax parsing.
    Diagnostics getParseDiagnostics();

    /// Gets the diagnostics produced during semantic analysis, including the binding of
    /// symbols, type checking, and name lookup. Note that this will force evaluation of
    /// any symbols or expressions that were still waiting for lazy evaluation.
    Diagnostics getSemanticDiagnostics();

    /// Gets all of the diagnostics produced during compilation.
    Diagnostics getAllDiagnostics();

    /// Report an error at the specified location.
    Diagnostic& addError(DiagCode code, SourceLocation location) { return diags.add(code, location); }
    Diagnostic& addError(DiagCode code, SourceRange sourceRange) { return diags.add(code, sourceRange); }

    /// Adds a set of diagnostics to the compilation's list of semantic diagnostics.
    void addDiagnostics(const Diagnostics& diagnostics);

    const Type& getType(SyntaxKind kind) const;
    const Type& getType(const DataTypeSyntax& node, LookupLocation location, const Scope& parent);
    const PackedArrayType& getType(bitwidth_t width, bool isSigned, bool isFourState = true, bool isReg = false);
    const ScalarType& getScalarType(bool isFourState, bool isReg = false);

    /// Various built-in type symbols for easy access.
    const ScalarType& getBitType() const { return bitType; }
    const ScalarType& getLogicType() const { return logicType; }
    const ScalarType& getRegType() const { return regType; }
    const PredefinedIntegerType& getShortIntType() const { return shortIntType; }
    const PredefinedIntegerType& getIntType() const { return intType; }
    const PredefinedIntegerType& getLongIntType() const { return longIntType; }
    const PredefinedIntegerType& getByteType() const { return byteType; }
    const PredefinedIntegerType& getIntegerType() const { return integerType; }
    const PredefinedIntegerType& getTimeType() const { return timeType; }
    const FloatingType& getRealType() const { return realType; }
    const FloatingType& getRealTimeType() const { return realTimeType; }
    const FloatingType& getShortRealType() const { return shortRealType; }
    const StringType& getStringType() const { return stringType; }
    const CHandleType& getCHandleType() const { return chandleType; }
    const VoidType& getVoidType() const { return voidType; }
    const NullType& getNullType() const { return nullType; }
    const EventType& getEventType() const { return eventType; }
    const ErrorType& getErrorType() const { return errorType; }

    ConstantValue* createConstant(ConstantValue&& value) { return constantAllocator.emplace(std::move(value)); }

    const Expression& bindExpression(const ExpressionSyntax& syntax, const BindContext& context);
    const Expression& bindAssignment(const Type& lhs, const ExpressionSyntax& rhs, SourceLocation location,
                                     const BindContext& context);

private:
    SubroutineSymbol& createSystemFunction(string_view name, SystemFunction kind,
                                           std::initializer_list<const Type*> argTypes);

    void getParamDecls(const ParameterDeclarationSyntax& syntax, bool isPort, bool isLocal,
                       SmallVector<Definition::ParameterDecl>& parameters);

    // These functions are called by Scopes to create and track various members.
    friend class Scope;
    SymbolMap* allocSymbolMap() { return symbolMapAllocator.emplace(); }
    Scope::DeferredMemberData& getOrAddDeferredData(Scope::DeferredMemberIndex& index);
    void trackImport(Scope::ImportDataIndex& index, const WildcardImportSymbol& import);
    span<const WildcardImportSymbol*> queryImports(Scope::ImportDataIndex index);

    // These functions are used for traversing the syntax hierarchy and finding all instantiations.
    using NameSet = flat_hash_set<string_view>;
    static void findInstantiations(const ModuleDeclarationSyntax& module,
                                   SmallVector<NameSet>& scopeStack, NameSet& found);
    static void findInstantiations(const MemberSyntax& node, SmallVector<NameSet>& scopeStack, NameSet& found);

    Diagnostics diags;
    std::unique_ptr<RootSymbol> root;
    const SourceManager* sourceManager = nullptr;
    bool finalized = false;
    bool forcedDiagnostics = false;

    // A set of names that are instantiated anywhere in the design. This is used to
    // determine which modules should be top-level instances (because nobody ever
    // instantiates them).
    NameSet instantiatedNames;

    // A list of compilation units that have been added to the compilation.
    std::vector<const CompilationUnitSymbol*> compilationUnits;

    // Storage for syntax trees that have been added to the compilation.
    std::vector<std::shared_ptr<SyntaxTree>> syntaxTrees;

    // Specialized allocators for types that are not trivially destructible.
    TypedBumpAllocator<SymbolMap> symbolMapAllocator;
    TypedBumpAllocator<ConstantValue> constantAllocator;

    // Sideband data for scopes that have deferred members.
    SafeIndexedVector<Scope::DeferredMemberData, Scope::DeferredMemberIndex> deferredData;

    // Sideband data for scopes that have wildcard imports. The list of imports
    // is stored here and queried during name lookups.
    SafeIndexedVector<Scope::ImportData, Scope::ImportDataIndex> importData;

    // The name map for global definitions.
    flat_hash_map<std::tuple<string_view, const Scope*>, std::unique_ptr<Definition>> definitionMap;

    // The name map for packages. Note that packages have their own namespace,
    // which is why they can't share the definitions name table.
    flat_hash_map<string_view, const PackageSymbol*> packageMap;

    // A cache of vector types, keyed on various properties such as bit width.
    flat_hash_map<uint32_t, const PackedArrayType*> vectorTypeCache;

    // Map from syntax kinds to the built-in types.
    flat_hash_map<SyntaxKind, const Type*> knownTypes;

    // Instances of all the built-in types.
    ScalarType bitType;
    ScalarType logicType;
    ScalarType regType;
    PredefinedIntegerType shortIntType;
    PredefinedIntegerType intType;
    PredefinedIntegerType longIntType;
    PredefinedIntegerType byteType;
    PredefinedIntegerType integerType;
    PredefinedIntegerType timeType;
    FloatingType realType;
    FloatingType realTimeType;
    FloatingType shortRealType;
    StringType stringType;
    CHandleType chandleType;
    VoidType voidType;
    NullType nullType;
    EventType eventType;
    ErrorType errorType;
};

}