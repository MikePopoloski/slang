//------------------------------------------------------------------------------
//! @file Compilation.h
//! @brief Central manager for compilation processes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <memory>

#include "slang/ast/InstancePath.h"
#include "slang/ast/Scope.h"
#include "slang/ast/Symbol.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/numeric/Time.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/util/Bag.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/IntervalMap.h"
#include "slang/util/SafeIndexedVector.h"

namespace slang::syntax {

class SyntaxTree;

}

namespace slang::ast {

class AttributeSymbol;
class ASTContext;
class CompilationUnitSymbol;
class Definition;
class Expression;
class GenericClassDefSymbol;
class InterfacePortSymbol;
class MethodPrototypeSymbol;
class ModportSymbol;
class PackageSymbol;
class PrimitiveSymbol;
class PortConnection;
class RootSymbol;
class Statement;
class SubroutineSymbol;
class SystemSubroutine;
class ValueDriver;

using DriverIntervalMap = IntervalMap<uint32_t, const ValueDriver*>;
using UnrollIntervalMap = IntervalMap<uint32_t, std::monostate>;

enum class IntegralFlags : uint8_t;
enum class UnconnectedDrive;

/// Specifies which set of min:typ:max expressions should
/// be used during compilation.
enum class SLANG_EXPORT MinTypMax {
    /// Use the "min" delay expressions.
    Min,

    /// Use the "typical" delay expressions.
    Typ,

    /// Use the "max" delay expressions.
    Max
};

/// Contains various options that can control compilation behavior.
struct SLANG_EXPORT CompilationOptions {
    /// The maximum depth of nested module instances (and interfaces/programs),
    /// to detect infinite recursion.
    uint32_t maxInstanceDepth = 128;

    /// The maximum number of steps that will be taken when expanding a single
    /// generate construct, to detect infinite loops.
    uint32_t maxGenerateSteps = 131072;

    /// The maximum depth of nested function calls in constant expressions,
    /// to detect infinite recursion.
    uint32_t maxConstexprDepth = 128;

    /// The maximum number of steps to allow when evaluating a constant expressions,
    /// to detect infinite loops.
    uint32_t maxConstexprSteps = 100000;

    /// The maximum number of frames in a callstack to display in diagnostics
    /// before abbreviating them.
    uint32_t maxConstexprBacktrace = 10;

    /// The maximum number of iterations to try to resolve defparams before
    /// giving up due to potentially cyclic dependencies in parameter values.
    uint32_t maxDefParamSteps = 128;

    /// The maximum number of instances allowed in a single instance array.
    uint32_t maxInstanceArray = 65535;

    /// The maximum number of errors that can be found before we short circuit
    /// the tree walking process.
    uint32_t errorLimit = 64;

    /// The maximum number of times we'll attempt to do typo correction before
    /// giving up. This is to prevent very slow compilation times if the
    /// source text is hopelessly broken.
    uint32_t typoCorrectionLimit = 32;

    /// Specifies which set of min:typ:max expressions should
    /// be used during compilation.
    MinTypMax minTypMax = MinTypMax::Typ;

    /// If true, allow hierarchical names in constant expressions.
    bool allowHierarchicalConst = false;

    /// If true, allow all integral types to convert implicitly to enum types.
    bool relaxEnumConversions = false;

    /// If true, allow symbols to be referenced before they're declared,
    /// even if that would otherwise be an error in SystemVerilog.
    bool allowUseBeforeDeclare = false;

    /// Signals driven by an always_comb are normally not allowed to be driven
    /// by any other process. Setting this option allows initial blocks to
    /// also drive such signals.
    bool allowDupInitialDrivers = false;

    /// If true, perform strict checking of variable drivers, which currently
    /// means not taking into account procedural for loop unrolling.
    bool strictDriverChecking = false;

    /// If true, compile in "linting" mode where we suppress errors that could
    /// be caused by not having an elaborated design.
    bool lintMode = false;

    /// If true, suppress warnings about unused code elements.
    bool suppressUnused = true;

    /// If true, don't issue an error when encountering an instantiation
    /// for an unknown definition.
    bool ignoreUnknownModules = false;

    /// When in script mode, suppress some errors that are otherwise pretty
    /// annoying when not in a batch context. For example, top-level modules
    /// that have interface ports will cause an error if this is not set.
    bool scriptMode = true;

    /// The default time scale to use for design elements that don't specify
    /// one explicitly.
    std::optional<TimeScale> defaultTimeScale;

    /// If non-empty, specifies the list of modules that should serve as the
    /// top modules in the design. If empty, this will be automatically determined
    /// based on which modules are unreferenced elsewhere.
    flat_hash_set<string_view> topModules;

    /// A list of parameters to override, of the form &lt;name>=&lt;value> -- note that
    /// for now at least this only applies to parameters in top-level modules.
    std::vector<std::string> paramOverrides;
};

/// A node in a tree representing an instance in the design
/// hierarchy where parameters should be overriden and/or
/// bind directives should be applied. These are assembled
/// from defparam values, bind directives, and command-line
/// specified overrides.
struct HierarchyOverrideNode {
    /// A map of parameters in the current scope to override.
    /// The key is the syntax node representing the parameter and the value is a pair,
    /// the first element of which is the value to set the parameter to and the second
    /// is the source defparam doing the overriding, if any (can be null).
    flat_hash_map<const syntax::SyntaxNode*, std::pair<ConstantValue, const syntax::SyntaxNode*>>
        overrides;

    /// A map of child scopes that also contain overrides.
    flat_hash_map<InstancePath::Entry, HierarchyOverrideNode> childNodes;

    /// A list of bind directives to apply in this scope.
    std::vector<const syntax::BindDirectiveSyntax*> binds;
};

/// A centralized location for creating and caching symbols. This includes
/// creating symbols from syntax nodes as well as fabricating them synthetically.
/// Common symbols such as built in types are exposed here as well.
class SLANG_EXPORT Compilation : public BumpAllocator {
public:
    explicit Compilation(const Bag& options = {});
    Compilation(const Compilation& other) = delete;
    Compilation(Compilation&& other) = delete;
    ~Compilation();

    /// Gets the set of options used to construct the compilation.
    const CompilationOptions& getOptions() const { return options; }

    /// Adds a syntax tree to the compilation. If the compilation has already been finalized
    /// by calling @a getRoot this call will throw an exception.
    void addSyntaxTree(std::shared_ptr<syntax::SyntaxTree> tree);

    /// Gets the set of syntax trees that have been added to the compilation.
    span<const std::shared_ptr<syntax::SyntaxTree>> getSyntaxTrees() const;

    /// Gets the compilation unit for the given syntax node. The compilation unit must have
    /// already been added to the compilation previously via a call to @a addSyntaxTree
    const CompilationUnitSymbol* getCompilationUnit(
        const syntax::CompilationUnitSyntax& syntax) const;

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
    /// This takes into account the given scope so that nested definitions are found
    /// before more global ones.
    const Definition* getDefinition(string_view name, const Scope& scope) const;

    /// Gets the definition for the given syntax node, or nullptr if it does not exist.
    const Definition* getDefinition(const syntax::ModuleDeclarationSyntax& syntax) const;

    /// Creates a new definition in the given scope based on the given syntax.
    void createDefinition(const Scope& scope, LookupLocation location,
                          const syntax::ModuleDeclarationSyntax& syntax);

    /// Gets the package with the give name, or null if there is no such package.
    const PackageSymbol* getPackage(string_view name) const;

    /// Gets the built-in 'std' package.
    const PackageSymbol& getStdPackage() const { return *stdPkg; }

    /// Creates a new package in the given scope based on the given syntax.
    const PackageSymbol& createPackage(const Scope& scope,
                                       const syntax::ModuleDeclarationSyntax& syntax);

    /// Gets the primitive with the given name, or null if there is no such primitive.
    const PrimitiveSymbol* getPrimitive(string_view name) const;

    /// Creates a new primitive in the given scope based on the given syntax.
    const PrimitiveSymbol& createPrimitive(const Scope& scope,
                                           const syntax::UdpDeclarationSyntax& syntax);

    /// Registers a built-in gate symbol.
    void addGateType(const PrimitiveSymbol& primitive);

    /// Gets the built-in gate type with the given name, or null if there is no such gate.
    const PrimitiveSymbol* getGateType(string_view name) const;

    /// Registers a system subroutine handler, which can be accessed by compiled code.
    void addSystemSubroutine(std::unique_ptr<SystemSubroutine> subroutine);

    /// Registers an externally owned system subroutine handler,
    /// which can be accessed by compiled code.
    void addSystemSubroutine(const SystemSubroutine& subroutine);

    /// Registers a type-based system method handler, which can be accessed by compiled code.
    void addSystemMethod(SymbolKind typeKind, std::unique_ptr<SystemSubroutine> method);

    /// Registers an externally owned type-based system method handler,
    /// which can be accessed by compiled code.
    void addSystemMethod(SymbolKind typeKind, const SystemSubroutine& subroutine);

    /// Gets a system subroutine with the given name, or null if there is no such subroutine
    /// registered.
    const SystemSubroutine* getSystemSubroutine(string_view name) const;

    /// Gets a system method for the specified type with the given name, or null if there is no such
    /// method registered.
    const SystemSubroutine* getSystemMethod(SymbolKind typeKind, string_view name) const;

    /// Sets the attributes associated with the given symbol.
    void setAttributes(const Symbol& symbol, span<const AttributeSymbol* const> attributes);

    /// Sets the attributes associated with the given statement.
    void setAttributes(const Statement& stmt, span<const AttributeSymbol* const> attributes);

    /// Sets the attributes associated with the given expression.
    void setAttributes(const Expression& expr, span<const AttributeSymbol* const> attributes);

    /// Sets the attributes associated with the given port connection.
    void setAttributes(const PortConnection& conn, span<const AttributeSymbol* const> attributes);

    /// Gets the attributes associated with the given symbol.
    span<const AttributeSymbol* const> getAttributes(const Symbol& symbol) const;

    /// Gets the attributes associated with the given statement.
    span<const AttributeSymbol* const> getAttributes(const Statement& stmt) const;

    /// Gets the attributes associated with the given expression.
    span<const AttributeSymbol* const> getAttributes(const Expression& expr) const;

    /// Gets the attributes associated with the given port connection.
    span<const AttributeSymbol* const> getAttributes(const PortConnection& conn) const;

    /// Notes that the given symbol was imported into the current scope via a package import,
    /// and further that the current scope is within a package declaration. These symbols are
    /// candidates for being exported from this package.
    void notePackageExportCandidate(const PackageSymbol& packageScope, const Symbol& symbol);

    /// Tries to find a symbol that can be exported from the given package to satisfy an import
    /// of a given name from that package. Returns nullptr if no such symbol can be found.
    const Symbol* findPackageExportCandidate(const PackageSymbol& packageScope,
                                             string_view name) const;

    /// Notes the presence of a bind directive. These can be later checked during
    /// scope elaboration to include the newly bound instances.
    void noteBindDirective(const syntax::BindDirectiveSyntax& syntax, const Scope& scope);

    /// Notes an instance that contains a bind directive targeting a global definition.
    /// These are later checked for correctness of type params.
    void noteInstanceWithDefBind(const Symbol& instance);

    /// Notes the presence of a DPI export directive. These will be checked for correctness
    /// but are otherwise unused by SystemVerilog code.
    void noteDPIExportDirective(const syntax::DPIExportSyntax& syntax, const Scope& scope);

    /// Tracks the existence of an out-of-block declaration (method or constraint) in the
    /// given scope. This can later be retrieved by calling findOutOfBlockDecl().
    void addOutOfBlockDecl(const Scope& scope, const syntax::ScopedNameSyntax& name,
                           const syntax::SyntaxNode& syntax, SymbolIndex index);

    /// Searches for an out-of-block declaration in the given @a scope with @a declName
    /// for a @a className class. Returns a tuple of syntax pointer and symbol
    /// index in the defining scope, along with a pointer that should be set to true if
    /// the resulting decl is considered "used". If not found, the syntax pointer will be null.
    std::tuple<const syntax::SyntaxNode*, SymbolIndex, bool*> findOutOfBlockDecl(
        const Scope& scope, string_view className, string_view declName) const;

    /// Tracks the existence of an extern interface method implementation. These are later
    /// elaborated by the compilation to hook up connections to their interface prototypes.
    void addExternInterfaceMethod(const SubroutineSymbol& method);

    /// Notes that there is a default clocking block associated with the specified scope.
    void noteDefaultClocking(const Scope& scope, const Symbol& clocking, SourceRange range);

    /// Notes that there is a default clocking block associated with the specified scope.
    void noteDefaultClocking(const ASTContext& context,
                             const syntax::DefaultClockingReferenceSyntax& syntax);

    /// Finds an applicable default clocking block for the given scope, or returns nullptr
    /// if no default clocking is in effect.
    const Symbol* getDefaultClocking(const Scope& scope) const;

    /// Notes that there is a global clocking block associated with the specified scope.
    void noteGlobalClocking(const Scope& scope, const Symbol& clocking, SourceRange range);

    /// Finds an applicable global clocking block for the given scope, or returns nullptr
    /// if no global clocking is in effect.
    const Symbol* getGlobalClocking(const Scope& scope) const;

    /// Notes that there is a default disable associated with the specified scope.
    void noteDefaultDisable(const Scope& scope, const Expression& expr);

    /// Finds an applicable default disable expression for the given scope, or returns nullptr
    /// if no such declaration is in effect.
    const Expression* getDefaultDisable(const Scope& scope) const;

    /// Notes that the given syntax node is "referenced" somewhere in the AST.
    /// This is used to diagnose unused variables, nets, etc. The @a isLValue parameter
    /// is used to tell whether a value is only assigned or whether it's also read somewhere.
    void noteReference(const syntax::SyntaxNode& node, bool isLValue = false);

    /// Notes that the given symbol is "referenced" somewhere in the AST.
    /// This is used to diagnose unused variables, nets, etc. The @a isLValue parameter
    /// is used to tell whether a value is only assigned or whether it's also read somewhere.
    void noteReference(const Symbol& symbol, bool isLValue = false);

    /// Checks whether the given syntax node has been referenced in the AST thus far.
    /// The result is a pair, the first item of which is true if the node has been used
    /// as a non-lvalue, and the second of which is true if the node has been used as an lvalue.
    /// The second item is only relevant for nodes where it makes sense; e.g. variables and nets.
    std::pair<bool, bool> isReferenced(const syntax::SyntaxNode& node) const;

    /// Notes that the given symbol has a name conflict in its parent scope.
    /// This will cause appropriate errors to be issued.
    void noteNameConflict(const Symbol& symbol);

    /// A convenience method for parsing a name string and turning it into a set
    /// of syntax nodes. This is mostly for testing and API purposes; normal
    /// compilation never does this.
    /// Throws an exception if there are errors parsing the name.
    const syntax::NameSyntax& parseName(string_view name);

    /// A convenience method for parsing a name string and turning it into a set
    /// of syntax nodes. This is mostly for testing and API purposes. Errors are
    /// added to the provided diagnostics bag.
    const syntax::NameSyntax& tryParseName(string_view name, Diagnostics& diags);

    /// Creates a new compilation unit within the design that can be modified dynamically,
    /// which is useful in runtime scripting scenarios. Note that this call will succeed
    /// even if the design has been finalized, but in that case any instantiations in the
    /// script scope won't affect which modules are determined to be top-level instances.
    CompilationUnitSymbol& createScriptScope();

    /// Gets the source manager associated with the compilation. If no syntax trees have
    /// been added to the design this method will return null.
    const SourceManager* getSourceManager() const { return sourceManager; }

    /// Gets the diagnostics produced during lexing, preprocessing, and syntax parsing.
    const Diagnostics& getParseDiagnostics();

    /// Gets the diagnostics produced during semantic analysis, including the creation of
    /// symbols, type checking, and name lookup. Note that this will finalize the compilation,
    /// including forcing the evaluation of any symbols or expressions that were still waiting
    /// for lazy evaluation.
    const Diagnostics& getSemanticDiagnostics();

    /// Gets all of the diagnostics produced during compilation.
    const Diagnostics& getAllDiagnostics();

    /// Adds a set of diagnostics to the compilation's list of semantic diagnostics.
    void addDiagnostics(const Diagnostics& diagnostics);

    /// Gets the default time scale to use when none is specified in the source code.
    std::optional<TimeScale> getDefaultTimeScale() const { return options.defaultTimeScale; }

    const Type& getType(syntax::SyntaxKind kind) const;
    const Type& getType(const syntax::DataTypeSyntax& node, const ASTContext& context,
                        const Type* typedefTarget = nullptr);
    const Type& getType(const Type& elementType,
                        const syntax::SyntaxList<syntax::VariableDimensionSyntax>& dimensions,
                        const ASTContext& context);

    const Type& getType(bitwidth_t width, bitmask<IntegralFlags> flags);
    const Type& getScalarType(bitmask<IntegralFlags> flags);
    const NetType& getNetType(parsing::TokenKind kind) const;

    /// Various built-in type symbols for easy access.
    const Type& getBitType() const { return *bitType; }
    const Type& getLogicType() const { return *logicType; }
    const Type& getIntType() const { return *intType; }
    const Type& getByteType() const { return *byteType; }
    const Type& getIntegerType() const { return *integerType; }
    const Type& getRealType() const { return *realType; }
    const Type& getShortRealType() const { return *shortRealType; }
    const Type& getStringType() const { return *stringType; }
    const Type& getVoidType() const { return *voidType; }
    const Type& getErrorType() const { return *errorType; }
    const Type& getUnsignedIntType();
    const Type& getNullType();
    const Type& getUnboundedType();
    const Type& getTypeRefType();

    /// Get the 'wire' built in net type. The rest of the built-in net types are rare enough
    /// that we don't bother providing dedicated accessors for them.
    const NetType& getWireNetType() const { return *wireNetType; }

    /// Allocates space for a constant value in the pool of constants.
    ConstantValue* allocConstant(ConstantValue&& value) {
        return constantAllocator.emplace(std::move(value));
    }

    /// Allocates a symbol map.
    SymbolMap* allocSymbolMap() { return symbolMapAllocator.emplace(); }

    /// Allocates a pointer map.
    PointerMap* allocPointerMap() { return pointerMapAllocator.emplace(); }

    /// Allocates a generic class symbol.
    template<typename... Args>
    GenericClassDefSymbol* allocGenericClass(Args&&... args) {
        return genericClassAllocator.emplace(std::forward<Args>(args)...);
    }

    DriverIntervalMap::allocator_type& getDriverMapAllocator() { return driverMapAllocator; }
    UnrollIntervalMap::allocator_type& getUnrollIntervalMapAllocator() {
        return unrollIntervalMapAllocator;
    }

    const syntax::ImplicitTypeSyntax& createEmptyTypeSyntax(SourceLocation loc);

    /// Forces the given symbol and all children underneath it in the hierarchy to
    /// be elaborated and any relevant diagnostics to be issued.
    void forceElaborate(const Symbol& symbol);

    int getNextEnumSystemId() { return nextEnumSystemId++; }
    int getNextStructSystemId() { return nextStructSystemId++; }
    int getNextUnionSystemId() { return nextUnionSystemId++; }

private:
    friend class Lookup;
    friend class Scope;

    // These functions are called by Scopes to create and track various members.
    Scope::DeferredMemberData& getOrAddDeferredData(Scope::DeferredMemberIndex& index);
    void trackImport(Scope::ImportDataIndex& index, const WildcardImportSymbol& import);
    span<const WildcardImportSymbol*> queryImports(Scope::ImportDataIndex index);

    bool doTypoCorrection() const { return typoCorrections < options.typoCorrectionLimit; }
    void didTypoCorrection() { typoCorrections++; }

    span<const AttributeSymbol* const> getAttributes(const void* ptr) const;

    Diagnostic& addDiag(Diagnostic diag);

    const RootSymbol& getRoot(bool skipDefParamsAndBinds);
    void parseParamOverrides(flat_hash_map<string_view, const ConstantValue*>& results);
    void checkDPIMethods(span<const SubroutineSymbol* const> dpiImports);
    void checkExternIfaceMethods(span<const MethodPrototypeSymbol* const> protos);
    void checkModportExports(
        span<const std::pair<const InterfacePortSymbol*, const ModportSymbol*>> modports);
    void checkElemTimeScale(std::optional<TimeScale> timeScale, SourceRange sourceRange);
    void resolveDefParamsAndBinds();
    void resolveBindTargets(const syntax::BindDirectiveSyntax& syntax, const Scope& scope,
                            SmallVector<const Symbol*>& instTargets, const Definition** defTarget);
    void checkBindTargetParams(const syntax::BindDirectiveSyntax& syntax, const Scope& scope,
                               span<const Symbol* const> instTargets, const Definition* defTarget);

    // Stored options object.
    CompilationOptions options;

    // Specialized allocators for types that are not trivially destructible.
    TypedBumpAllocator<SymbolMap> symbolMapAllocator;
    TypedBumpAllocator<PointerMap> pointerMapAllocator;
    TypedBumpAllocator<ConstantValue> constantAllocator;
    TypedBumpAllocator<GenericClassDefSymbol> genericClassAllocator;
    DriverIntervalMap::allocator_type driverMapAllocator;
    UnrollIntervalMap::allocator_type unrollIntervalMapAllocator;

    // A table to look up scalar types based on combinations of the three flags: signed, fourstate,
    // reg. Two of the entries are not valid and will be nullptr (!fourstate & reg).
    Type* scalarTypeTable[8]{nullptr};

    // Instances of all the built-in types.
    Type* bitType;
    Type* logicType;
    Type* intType;
    Type* byteType;
    Type* integerType;
    Type* realType;
    Type* shortRealType;
    Type* stringType;
    Type* voidType;
    Type* errorType;
    NetType* wireNetType;

    // Sideband data for scopes that have deferred members.
    SafeIndexedVector<Scope::DeferredMemberData, Scope::DeferredMemberIndex> deferredData;

    // Sideband data for scopes that have wildcard imports. The list of imports
    // is stored here and queried during name lookups.
    SafeIndexedVector<Scope::ImportData, Scope::ImportDataIndex> importData;

    // A map of syntax nodes that have been referenced in the AST.
    // The value indicates whether the node has been used as an lvalue vs non-lvalue,
    // for things like variables and nets.
    flat_hash_map<const syntax::SyntaxNode*, std::pair<bool, bool>> referenceStatusMap;

    // The lookup table for top-level modules. The value is a pair, with the second
    // element being a boolean indicating whether there exists at least one nested
    // module with the given name (requiring a more involved lookup).
    flat_hash_map<string_view, std::pair<Definition*, bool>> topDefinitions;

    // A cache of vector types, keyed on various properties such as bit width.
    flat_hash_map<uint32_t, const Type*> vectorTypeCache;

    // Map from syntax kinds to the built-in types.
    flat_hash_map<syntax::SyntaxKind, const Type*> knownTypes;

    // Map from token kinds to the built-in net types.
    flat_hash_map<parsing::TokenKind, std::unique_ptr<NetType>> knownNetTypes;

    // The name map for packages. Note that packages have their own namespace,
    // which is why they can't share the definitions name table.
    flat_hash_map<string_view, const PackageSymbol*> packageMap;

    // The name map for system subroutines.
    flat_hash_map<string_view, const SystemSubroutine*> subroutineMap;

    // The name map for system methods.
    flat_hash_map<std::tuple<string_view, SymbolKind>, const SystemSubroutine*> methodMap;

    // Map from pointers (to symbols, statements, expressions) to their associated attributes.
    flat_hash_map<const void*, span<const AttributeSymbol* const>> attributeMap;

    // A set of all instantiated names in the design; used for determining whether a given
    // module has ever been instantiated to know whether it should be considered top-level.
    flat_hash_set<string_view> globalInstantiations;

    struct DefinitionMetadata {
        const syntax::SyntaxTree* tree = nullptr;
        const NetType* defaultNetType = nullptr;
        std::optional<TimeScale> timeScale;
        UnconnectedDrive unconnectedDrive = UnconnectedDrive::None;
    };

    // Map from syntax nodes to parse-time metadata about them.
    flat_hash_map<const syntax::ModuleDeclarationSyntax*, DefinitionMetadata> definitionMetadata;

    // The name map for all module, interface, and program definitions.
    // The key is a combination of definition name + the scope in which it was declared.
    flat_hash_map<std::tuple<string_view, const Scope*>, Definition*> definitionMap;

    // A list of all created definitions, as storage for their memory.
    std::vector<std::unique_ptr<Definition>> definitionMemory;

    // A map from diag code + location to the diagnostics that have occurred at that location.
    // This is used to collapse duplicate diagnostics across instantiations into a single report.
    using DiagMap = flat_hash_map<std::tuple<DiagCode, SourceLocation>, std::vector<Diagnostic>>;
    DiagMap diagMap;

    // A map of packages to the set of names that are candidates for being
    // exported from those packages.
    flat_hash_map<const PackageSymbol*, flat_hash_map<string_view, const Symbol*>>
        packageExportCandidateMap;

    // A map from class name + decl name + scope to out-of-block declarations. These get
    // registered when we find the initial declaration and later get used when we see
    // the class prototype. The value also includes a boolean indicating whether anything
    // has used this declaration -- an error is issued if it's never used.
    mutable flat_hash_map<
        std::tuple<string_view, string_view, const Scope*>,
        std::tuple<const syntax::SyntaxNode*, const syntax::ScopedNameSyntax*, SymbolIndex, bool>>
        outOfBlockDecls;

    std::unique_ptr<RootSymbol> root;
    const SourceManager* sourceManager = nullptr;
    size_t numErrors = 0; // total number of errors inserted into the diagMap
    bool finalized = false;
    bool finalizing = false; // to prevent reentrant calls to getRoot()
    bool anyElemsWithTimescales = false;
    uint32_t typoCorrections = 0;
    int nextEnumSystemId = 1;
    int nextStructSystemId = 1;
    int nextUnionSystemId = 1;

    // This is storage for a temporary diagnostic that is being constructed.
    // Typically this is done in-place within the diagMap, but for diagnostics
    // that have been supressed we need space to return *something* to the caller.
    Diagnostic tempDiag;

    std::optional<Diagnostics> cachedParseDiagnostics;
    std::optional<Diagnostics> cachedSemanticDiagnostics;
    std::optional<Diagnostics> cachedAllDiagnostics;

    // A list of compilation units that have been added to the compilation.
    std::vector<const CompilationUnitSymbol*> compilationUnits;

    // Storage for syntax trees that have been added to the compilation.
    std::vector<std::shared_ptr<syntax::SyntaxTree>> syntaxTrees;

    // A list of definitions that are unreferenced in any instantiations and
    // are also not automatically instantiated as top-level.
    std::vector<const Definition*> unreferencedDefs;

    // The name map for user-defined primitive definitions.
    flat_hash_map<string_view, const PrimitiveSymbol*> udpMap;

    // The name map for built-in primitive definitions. These are stored in a separate
    // map because they are distinguished by keyword names that may otherwise collide
    // with escaped identifiers used by user code.
    flat_hash_map<string_view, const PrimitiveSymbol*> gateMap;

    // A map from syntax node to the definition it represents. Used much less frequently
    // than other ways of looking up definitions which is why it's lower down here.
    flat_hash_map<const syntax::ModuleDeclarationSyntax*, Definition*> definitionFromSyntax;

    // A tree of overrides to apply when elaborating.
    // Note that instances store pointers into this tree so it must not be
    // modified after elaboration begins.
    HierarchyOverrideNode hierarchyOverrides;

    // A list of DPI export directives we've encountered during elaboration.
    std::vector<std::pair<const syntax::DPIExportSyntax*, const Scope*>> dpiExports;

    // A list of bind directives we've encountered during elaboration.
    std::vector<std::pair<const syntax::BindDirectiveSyntax*, const Scope*>> bindDirectives;

    // A list of extern interface method implementations for later elaboration.
    std::vector<const SubroutineSymbol*> externInterfaceMethods;

    // A list of name conflicts to later resolve by issuing diagnostics.
    std::vector<const Symbol*> nameConflicts;

    // A map of scopes to default clocking blocks.
    flat_hash_map<const Scope*, const Symbol*> defaultClockingMap;

    // A map of scopes to global clocking blocks.
    flat_hash_map<const Scope*, const Symbol*> globalClockingMap;

    // A map of scopes to default disable declarations.
    flat_hash_map<const Scope*, const Expression*> defaultDisableMap;

    // A set of instances that have global definition-based bind directives applied.
    // This is pretty rare and only used for checking of type params.
    flat_hash_map<const Definition*, std::vector<const Symbol*>> instancesWithDefBinds;

    // Storage for system subroutine instances.
    std::vector<std::unique_ptr<SystemSubroutine>> subroutineStorage;

    // The built-in std package.
    const PackageSymbol* stdPkg = nullptr;
};

} // namespace slang::ast
