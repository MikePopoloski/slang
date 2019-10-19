//------------------------------------------------------------------------------
// Compilation.h
// Central manager for compilation processes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <memory>

#include "slang/diagnostics/Diagnostics.h"
#include "slang/numeric/Time.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/SafeIndexedVector.h"

namespace slang {

class CHandleType;
class CompilationUnitSymbol;
class DefinitionSymbol;
class ErrorType;
class EventType;
class Expression;
class FloatingType;
class NullType;
class PackageSymbol;
class PackedArrayType;
class PredefinedIntegerType;
class RootSymbol;
class ScalarType;
class Statement;
class StringType;
class SyntaxTree;
class SystemSubroutine;
class VoidType;

struct CompilationUnitSyntax;
struct ModuleDeclarationSyntax;

enum class IntegralFlags : uint8_t;

/// A centralized location for creating and caching symbols. This includes
/// creating symbols from syntax nodes as well as fabricating them synthetically.
/// Common symbols such as built in types are exposed here as well.
class Compilation : public BumpAllocator {
public:
    Compilation();
    ~Compilation();

    /// Adds a syntax tree to the compilation. If the compilation has already been finalized
    /// by calling @a getRoot this call will throw an exception.
    void addSyntaxTree(std::shared_ptr<SyntaxTree> tree);

    /// Gets the set of syntax trees that have been added to the compilation.
    span<const std::shared_ptr<SyntaxTree>> getSyntaxTrees() const;

    /// Gets the compilation unit for the given syntax node. The compilation unit must have
    /// already been added to the compilation previously via a call to @a addSyntaxTree
    const CompilationUnitSymbol* getCompilationUnit(const CompilationUnitSyntax& syntax) const;

    /// Gets the set of compilation units that have been added to the compilation.
    span<const CompilationUnitSymbol* const> getCompilationUnits() const;

    /// Gets the root of the design. The first time you call this method all top-level
    /// instances will be elaborated and the compilation finalized. After that you can
    /// no longer make any modifications to the compilation object; any attempts to do
    /// so will result in an exception.
    const RootSymbol& getRoot();

    /// Indicates whether the design has been compiled and can no longer accept modifications.
    bool isFinalized() const { return finalized; }

    /// Gets the definition with the given name, or null if there is no such definition.
    /// This takes into account the given scope so that nested definitions are found before more
    /// global ones.
    const DefinitionSymbol* getDefinition(string_view name, const Scope& scope) const;

    /// Gets the top level definition with the given name, or null if there is no such definition.
    const DefinitionSymbol* getDefinition(string_view name) const;

    /// Adds a definition to the set of definitions tracked in the compilation.
    void addDefinition(const DefinitionSymbol& definition);

    /// Gets the package with the give name, or null if there is no such package.
    const PackageSymbol* getPackage(string_view name) const;

    /// Adds a package to the map of global packages.
    void addPackage(const PackageSymbol& package);

    /// Registers a system subroutine handler, which can be accessed by compiled code.
    void addSystemSubroutine(std::unique_ptr<SystemSubroutine> subroutine);

    /// Registers a type-based system method handler, which can be accessed by compiled code.
    void addSystemMethod(SymbolKind typeKind, std::unique_ptr<SystemSubroutine> method);

    /// Gets a system subroutine with the given name, or null if there is no such subroutine
    /// registered.
    const SystemSubroutine* getSystemSubroutine(string_view name) const;

    /// Gets a system method for the specified type with the given name, or null if there is no such
    /// method registered.
    const SystemSubroutine* getSystemMethod(SymbolKind typeKind, string_view name) const;

    /// Sets the attributes associated with the given symbol.
    void addAttributes(const Symbol& symbol, span<const AttributeInstanceSyntax* const> syntax);

    /// Sets the attributes associated with the given statement.
    void addAttributes(const Statement& stmt, span<const AttributeInstanceSyntax* const> syntax);

    /// Sets the attributes associated with the given expression.
    void addAttributes(const Expression& expr, span<const AttributeInstanceSyntax* const> syntax);

    /// Gets the attributes associated with the given symbol.
    span<const AttributeSymbol* const> getAttributes(const Symbol& symbol) const;

    /// Gets the attributes associated with the given statement.
    span<const AttributeSymbol* const> getAttributes(const Statement& stmt) const;

    /// Gets the attributes associated with the given expression.
    span<const AttributeSymbol* const> getAttributes(const Expression& expr) const;

    /// A convenience method for parsing a name string and turning it into a set of syntax nodes.
    /// This is mostly for testing and API purposes; normal compilation never does this.
    /// Throws an exception if there are errors parsing the name.
    const NameSyntax& parseName(string_view name);

    /// Creates a new compilation unit within the design that can be modified dynamically,
    /// which is useful in runtime scripting scenarios. Note that this call will succeed
    /// even if the design has been finalized, but in that case any instantiations in the
    /// script scope won't affect which modules are determined to be top-level instances.
    CompilationUnitSymbol& createScriptScope();

    /// Gets a reference to an empty compilation unit, which can be useful for binding
    /// in cases where you don't care about the context.
    const CompilationUnitSymbol& getEmptyUnit() const { return *emptyUnit; }

    /// Gets the source manager associated with the compilation. If no syntax trees have
    /// been added to the design this method will return null.
    const SourceManager* getSourceManager() const { return sourceManager; }

    /// Gets the diagnostics produced during lexing, preprocessing, and syntax parsing.
    const Diagnostics& getParseDiagnostics();

    /// Gets the diagnostics produced during semantic analysis, including the binding of
    /// symbols, type checking, and name lookup. Note that this will finalize the compilation,
    /// including forcing the evaluation of any symbols or expressions that were still waiting
    /// for lazy evaluation.
    const Diagnostics& getSemanticDiagnostics();

    /// Gets all of the diagnostics produced during compilation.
    const Diagnostics& getAllDiagnostics();

    /// Adds a set of diagnostics to the compilation's list of semantic diagnostics.
    void addDiagnostics(const Diagnostics& diagnostics);

    /// Gets the default net type that was in place at the time the given declaration was parsed.
    const NetType& getDefaultNetType(const ModuleDeclarationSyntax& decl) const;

    /// Gets the time scale that was put in place by a preprocessor directive at the time
    /// the given declaration was parsed. Returns nullopt if there was no such directive.
    optional<TimeScale> getDirectiveTimeScale(const ModuleDeclarationSyntax& decl) const;

    /// Sets the default time scale to use when none is specified in the source code.
    void setDefaultTimeScale(TimeScale timeScale) { defaultTimeScale = timeScale; }

    /// Gets the default time scale to use when none is specified in the source code.
    TimeScale getDefaultTimeScale() const { return defaultTimeScale; }

    const Type& getType(SyntaxKind kind) const;
    const Type& getType(const DataTypeSyntax& node, LookupLocation location, const Scope& parent,
                        bool forceSigned = false);
    const Type& getType(const Type& elementType,
                        const SyntaxList<VariableDimensionSyntax>& dimensions,
                        LookupLocation location, const Scope& parent);

    const Type& getType(bitwidth_t width, bitmask<IntegralFlags> flags);
    const Type& getScalarType(bitmask<IntegralFlags> flags);
    const NetType& getNetType(TokenKind kind) const;

    /// Various built-in type symbols for easy access.
    const Type& getBitType() const { return *bitType; }
    const Type& getLogicType() const { return *logicType; }
    const Type& getRegType() const { return *regType; }
    const Type& getShortIntType() const { return *shortIntType; }
    const Type& getIntType() const { return *intType; }
    const Type& getLongIntType() const { return *longIntType; }
    const Type& getByteType() const { return *byteType; }
    const Type& getIntegerType() const { return *integerType; }
    const Type& getTimeType() const { return *timeType; }
    const Type& getRealType() const { return *realType; }
    const Type& getRealTimeType() const { return *realTimeType; }
    const Type& getShortRealType() const { return *shortRealType; }
    const Type& getStringType() const { return *stringType; }
    const Type& getCHandleType() const { return *chandleType; }
    const Type& getVoidType() const { return *voidType; }
    const Type& getNullType() const { return *nullType; }
    const Type& getEventType() const { return *eventType; }
    const Type& getErrorType() const { return *errorType; }
    const Type& getUnsignedIntType();

    /// Get the 'wire' built in net type. The rest of the built-in net types are rare enough
    /// that we don't bother providing dedicated accessors for them.
    const NetType& getWireNetType() const { return *wireNetType; }

    /// Allocates space for a constant value in the pool of constants.
    ConstantValue* allocConstant(ConstantValue&& value) {
        return constantAllocator.emplace(std::move(value));
    }

    /// Allocates a symbol map.
    SymbolMap* allocSymbolMap() { return symbolMapAllocator.emplace(); }

private:
    // These functions are called by Scopes to create and track various members.
    friend class Scope;
    Scope::DeferredMemberData& getOrAddDeferredData(Scope::DeferredMemberIndex& index);
    void trackImport(Scope::ImportDataIndex& index, const WildcardImportSymbol& import);
    span<const WildcardImportSymbol*> queryImports(Scope::ImportDataIndex index);

    bool isFinalizing() const { return finalizing; }

    void addAttributes(const void* ptr, span<const AttributeInstanceSyntax* const> syntax);
    span<const AttributeSymbol* const> getAttributes(const void* ptr) const;

    Diagnostics diags;
    std::unique_ptr<RootSymbol> root;
    CompilationUnitSymbol* emptyUnit = nullptr;
    const SourceManager* sourceManager = nullptr;
    TimeScale defaultTimeScale;
    bool finalized = false;
    bool finalizing = false; // to prevent reentrant calls to getRoot()

    optional<Diagnostics> cachedParseDiagnostics;
    optional<Diagnostics> cachedSemanticDiagnostics;
    optional<Diagnostics> cachedAllDiagnostics;

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

    // The name map for global definitions. The key is a combination of definition name +
    // the scope in which it was declared. The value is the definition symbol along with a
    // boolean that indicates whether it has ever been instantiated in the design.
    mutable flat_hash_map<std::tuple<string_view, const Scope*>,
                          std::tuple<const DefinitionSymbol*, bool>>
        definitionMap;

    // The name map for packages. Note that packages have their own namespace,
    // which is why they can't share the definitions name table.
    flat_hash_map<string_view, const PackageSymbol*> packageMap;

    // The name map for system subroutines.
    flat_hash_map<string_view, std::unique_ptr<SystemSubroutine>> subroutineMap;

    // The name map for system methods.
    flat_hash_map<std::tuple<string_view, SymbolKind>, std::unique_ptr<SystemSubroutine>> methodMap;

    // A cache of vector types, keyed on various properties such as bit width.
    flat_hash_map<uint32_t, const Type*> vectorTypeCache;

    // Map from syntax kinds to the built-in types.
    flat_hash_map<SyntaxKind, const Type*> knownTypes;

    // Map from token kinds to the built-in net types.
    flat_hash_map<TokenKind, std::unique_ptr<NetType>> knownNetTypes;

    // Map from syntax nodes to parse-time metadata about default net types.
    flat_hash_map<const ModuleDeclarationSyntax*, const NetType*> defaultNetTypeMap;

    // Map from syntax nodes to parse-time metadata about time scale directives.
    flat_hash_map<const ModuleDeclarationSyntax*, TimeScale> timeScaleDirectiveMap;

    // Map from pointers (to symbols, statements, expressions) to their associated attributes.
    flat_hash_map<const void*, span<const AttributeSymbol* const>> attributeMap;

    // A table to look up scalar types based on combinations of the three flags: signed, fourstate,
    // reg. Two of the entries are not valid and will be nullptr (!fourstate & reg).
    Type* scalarTypeTable[8]{ nullptr };

    // Instances of all the built-in types.
    Type* bitType;
    Type* logicType;
    Type* regType;
    Type* signedBitType;
    Type* signedLogicType;
    Type* signedRegType;
    Type* shortIntType;
    Type* intType;
    Type* longIntType;
    Type* byteType;
    Type* integerType;
    Type* timeType;
    Type* realType;
    Type* realTimeType;
    Type* shortRealType;
    Type* stringType;
    Type* chandleType;
    Type* voidType;
    Type* nullType;
    Type* eventType;
    Type* errorType;
    NetType* wireNetType;
};

} // namespace slang