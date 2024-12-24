//------------------------------------------------------------------------------
//! @file Compilation.h
//! @brief Central manager for compilation processes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <memory>

#include "slang/ast/OpaqueInstancePath.h"
#include "slang/ast/Scope.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/numeric/Time.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/util/Bag.h"
#include "slang/util/BumpAllocator.h"
#include "slang/util/IntervalMap.h"
#include "slang/util/LanguageVersion.h"
#include "slang/util/SafeIndexedVector.h"

namespace slang::syntax {
class SyntaxTree;
}

namespace slang::ast {

class AttributeSymbol;
class ASTContext;
class CompilationUnitSymbol;
class ConfigBlockSymbol;
class DefinitionSymbol;
class Expression;
class GenericClassDefSymbol;
class InstanceSymbol;
class InterfacePortSymbol;
class MethodPrototypeSymbol;
class ModportSymbol;
class PackageSymbol;
class PrimitiveSymbol;
class PortConnection;
class RootSymbol;
class Statement;
class SubroutineSymbol;
class Symbol;
class SystemSubroutine;
class ValueDriver;
struct AssertionInstanceDetails;
struct ConfigRule;
struct ResolvedConfig;

using DriverIntervalMap = IntervalMap<uint64_t, const ValueDriver*>;
using UnrollIntervalMap = IntervalMap<uint64_t, std::monostate>;
using DriverBitRange = std::pair<uint64_t, uint64_t>;

enum class IntegralFlags : uint8_t;
enum class SymbolIndex : uint32_t;
enum class SymbolKind : int;
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

/// Defines flags that control compilation behavior.
enum class SLANG_EXPORT CompilationFlags {
    /// No flags specified.
    None = 0,

    /// Allow hierarchical names in constant expressions.
    AllowHierarchicalConst = 1 << 0,

    /// Allow all integral types to convert implicitly to enum types.
    RelaxEnumConversions = 1 << 1,

    /// Allow symbols to be referenced before they're declared,
    /// even if that would otherwise be an error in SystemVerilog.
    AllowUseBeforeDeclare = 1 << 2,

    /// Signals driven by an always_comb are normally not allowed to be driven
    /// by any other process. This flag allows initial blocks to
    /// also drive such signals.
    AllowDupInitialDrivers = 1 << 3,

    /// Allow top-level modules to have interface ports. This is not allowed in
    /// standard SystemVerilog but it defaults to true to make using the API in
    /// scripting / programmatic modes more convenient.
    AllowTopLevelIfacePorts = 1 << 4,

    /// Perform strict checking of variable drivers, which currently
    /// means not taking into account procedural for loop unrolling.
    StrictDriverChecking = 1 << 5,

    /// Compile in "linting" mode where we suppress errors that could
    /// be caused by not having an elaborated design.
    LintMode = 1 << 6,

    /// Suppress warnings about unused code elements.
    SuppressUnused = 1 << 7,

    /// Don't issue an error when encountering an instantiation
    /// for an unknown definition.
    IgnoreUnknownModules = 1 << 8,

    /// Allow strings to implicitly convert to integers.
    RelaxStringConversions = 1 << 9,

    /// Allow implicit call expressions (lacking parentheses) to be recursive function calls.
    AllowRecursiveImplicitCall = 1 << 10,

    /// Allow module parameter assignments to elide the parentheses.
    AllowBareValParamAssignment = 1 << 11,

    /// Allow self-determined streaming concatenation expressions; normally these
    /// can only be used in specific assignment-like contexts.
    AllowSelfDeterminedStreamConcat = 1 << 12,

    /// Allow multi-driven subroutine local variables.
    AllowMultiDrivenLocals = 1 << 13,

    /// Allow merging ANSI port declarations with nets and variables
    /// declared in the module body.
    AllowMergingAnsiPorts = 1 << 14,

    /// Disable the use of instance caching, which normally allows skipping
    /// duplicate instance bodies to save time when elaborating.
    DisableInstanceCaching = 1 << 15,
};
SLANG_BITMASK(CompilationFlags, DisableInstanceCaching)

/// Contains various options that can control compilation behavior.
struct SLANG_EXPORT CompilationOptions {
    /// Various flags that control compilation behavior.
    bitmask<CompilationFlags> flags = CompilationFlags::AllowTopLevelIfacePorts |
                                      CompilationFlags::SuppressUnused;

    /// The maximum depth of nested module instances (and interfaces/programs),
    /// to detect infinite recursion.
    uint32_t maxInstanceDepth = 128;

    /// The maximum depth of nested checker instances to detect infinite recursion.
    uint32_t maxCheckerInstanceDepth = 64;

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

    /// The maximum depth of recursive generic class specializations.
    uint32_t maxRecursiveClassSpecialization = 8;

    /// The maximum number of UDP coverage notes that will be generated for a single
    /// warning about missing edge transitions.
    uint32_t maxUDPCoverageNotes = 8;

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

    /// The version of the SystemVerilog language to use.
    LanguageVersion languageVersion = LanguageVersion::Default;

    /// The default time scale to use for design elements that don't specify
    /// one explicitly.
    std::optional<TimeScale> defaultTimeScale;

    /// If non-empty, specifies the list of modules that should serve as the
    /// top modules in the design. If empty, this will be automatically determined
    /// based on which modules are unreferenced elsewhere.
    flat_hash_set<std::string_view> topModules;

    /// A list of parameters to override, of the form &lt;name>=&lt;value> -- note that
    /// for now at least this only applies to parameters in top-level modules.
    std::vector<std::string> paramOverrides;

    /// A list of library names, in the order in which they should be searched
    /// when binding cells to instances.
    std::vector<std::string> defaultLiblist;
};

/// Information about how a bind directive applies to some definition
/// or specific target node.
struct SLANG_EXPORT BindDirectiveInfo {
    /// The syntax node of the bind directive.
    const syntax::BindDirectiveSyntax* bindSyntax = nullptr;

    /// The syntax node for a config rule that applies
    /// to the target instance, if any.
    const syntax::SyntaxNode* configRuleSyntax = nullptr;

    /// The syntax node for a config block that applies
    /// to the target instance, if any.
    const syntax::SyntaxNode* configBlockSyntax = nullptr;

    /// The syntax node for the resolved definition,
    /// if definition name resolution succeeded.
    const syntax::SyntaxNode* instantiationDefSyntax = nullptr;

    /// A liblist that applies to the newly bound instance.
    std::span<const SourceLibrary* const> liblist;

    /// If true, the new instance is also a new config root,
    /// and @a configRootSyntax points to the config block
    /// for that root. Otherwise, it points either to nullptr,
    /// or to its parent's config root.
    bool isNewConfigRoot = false;
};

/// A node in a tree representing an instance in the design
/// hierarchy where parameters should be overriden and/or
/// bind directives should be applied. These are assembled
/// from defparam values, bind directives, and command-line
/// specified overrides.
struct SLANG_EXPORT HierarchyOverrideNode {
    /// A map of parameters in the current scope to override.
    /// The key is the syntax node representing the parameter and the value is a pair,
    /// the first element of which is the value to set the parameter to and the second
    /// is the source defparam doing the overriding, if any (can be null).
    flat_hash_map<const syntax::SyntaxNode*, std::pair<ConstantValue, const syntax::SyntaxNode*>>
        paramOverrides;

    /// A map of child scopes that also contain overrides.
    flat_hash_map<OpaqueInstancePath::Entry, HierarchyOverrideNode> childNodes;

    /// A list of bind directives to apply in this scope.
    /// The first entry is info about the bind instantiation, and the
    /// second is an optional pointer to the definition it targets.
    /// If the target is null, then the bind is actually targeting the
    /// scope represented by this override node.
    std::vector<std::pair<BindDirectiveInfo, const syntax::SyntaxNode*>> binds;
};

/// A centralized location for creating and caching symbols. This includes
/// creating symbols from syntax nodes as well as fabricating them synthetically.
/// Common symbols such as built in types are exposed here as well.
///
/// A Compilation object is the entry point for building ASTs. Typically you
/// add one or more SyntaxTrees to the compilation and then call getRoot() to
/// retrieve the root of the elaborated AST, and getAllDiagnostics() to get
/// a list of all diagnostics issued in the design.
///
class SLANG_EXPORT Compilation : public BumpAllocator {
public:
    /// Constructs a new instance of the Compilation class.
    explicit Compilation(const Bag& options = {}, const SourceLibrary* defaultLib = nullptr);
    Compilation(const Compilation& other) = delete;
    Compilation(Compilation&& other) = delete;
    ~Compilation();

    /// @name Top-level API
    /// @{

    /// Gets the set of options used to construct the compilation.
    const CompilationOptions& getOptions() const { return options; }

    /// Returns true if the given flag(s) are enabled for this compilation.
    bool hasFlag(bitmask<CompilationFlags> flags) const { return options.flags.has(flags); }

    /// Gets the language version set in the compilation options.
    LanguageVersion languageVersion() const { return getOptions().languageVersion; }

    /// Gets the source manager associated with the compilation. If no syntax trees have
    /// been added to the design this method will return nullptr.
    const SourceManager* getSourceManager() const { return sourceManager; }

    /// Adds a syntax tree to the compilation. If the compilation has already been finalized
    /// by calling @a getRoot this call will throw an exception.
    void addSyntaxTree(std::shared_ptr<syntax::SyntaxTree> tree);

    /// Gets the set of syntax trees that have been added to the compilation.
    std::span<const std::shared_ptr<syntax::SyntaxTree>> getSyntaxTrees() const;

    /// Gets the root of the design. The first time you call this method all top-level
    /// instances will be elaborated and the compilation finalized. After that you can
    /// no longer make any modifications to the compilation object; any attempts to do
    /// so will result in an exception.
    const RootSymbol& getRoot();

    /// Indicates whether the design has been compiled and can no longer accept modifications.
    bool isFinalized() const { return finalized; }

    /// Gets the diagnostics produced during lexing, preprocessing, and syntax parsing.
    const Diagnostics& getParseDiagnostics();

    /// Gets the diagnostics produced during semantic analysis, including the creation of
    /// symbols, type checking, and name lookup. Note that this will finalize the compilation,
    /// including forcing the evaluation of any symbols or expressions that were still waiting
    /// for lazy evaluation.
    const Diagnostics& getSemanticDiagnostics();

    /// Gets all of the diagnostics produced during compilation.
    const Diagnostics& getAllDiagnostics();

    /// Queries if any errors have been issued on any scope within this compilation.
    bool hasIssuedErrors() const { return numErrors > 0; };

    /// @}
    /// @name Utility and convenience methods
    /// @{

    /// A convenience method for parsing a name string and turning it into a set
    /// of syntax nodes. This is mostly for testing and API purposes; normal
    /// compilation never does this.
    /// Throws an exception if there are errors parsing the name.
    const syntax::NameSyntax& parseName(std::string_view name);

    /// A convenience method for parsing a name string and turning it into a set
    /// of syntax nodes. This is mostly for testing and API purposes. Errors are
    /// added to the provided diagnostics bag.
    const syntax::NameSyntax& tryParseName(std::string_view name, Diagnostics& diags);

    /// Creates a new compilation unit within the design that can be modified dynamically,
    /// which is useful in runtime scripting scenarios. Note that this call will succeed
    /// even if the design has been finalized, but in that case any instantiations in the
    /// script scope won't affect which modules are determined to be top-level instances.
    CompilationUnitSymbol& createScriptScope();

    /// @}
    /// @name Lookup and query methods
    /// @{

    /// Gets the compilation unit for the given syntax node. The compilation unit must have
    /// already been added to the compilation previously via a call to @a addSyntaxTree --
    /// otherwise returns nullptr.
    const CompilationUnitSymbol* getCompilationUnit(
        const syntax::CompilationUnitSyntax& syntax) const;

    /// Gets the set of compilation units that have been added to the compilation.
    std::span<const CompilationUnitSymbol* const> getCompilationUnits() const;

    /// Gets the source library with the given name, or nullptr if there is no such library.
    const SourceLibrary* getSourceLibrary(std::string_view name) const;

    /// Gets the default library object.
    const SourceLibrary& getDefaultLibrary() const { return *defaultLibPtr; }

    /// A struct containing the result of a definition lookup.
    struct DefinitionLookupResult {
        /// The definition that was found, or nullptr if none was found.
        const Symbol* definition = nullptr;

        /// A new config root that applies to this definition and
        /// any hierarchy underneath it, or nullptr if none.
        const ConfigBlockSymbol* configRoot = nullptr;

        /// A config rule that applies to instances using this
        /// definition, or nullptr if none.
        const ConfigRule* configRule = nullptr;

        DefinitionLookupResult() = default;

        DefinitionLookupResult(const Symbol* definition) : definition(definition) {}

        DefinitionLookupResult(const Symbol* definition, const ConfigBlockSymbol* configRoot,
                               const ConfigRule* configRule) :
            definition(definition), configRoot(configRoot), configRule(configRule) {}
    };

    /// Gets the definition with the given name, or nullptr if there is no such definition.
    /// This takes into account the given scope so that nested definitions are found
    /// before more global ones.
    DefinitionLookupResult tryGetDefinition(std::string_view name, const Scope& scope) const;

    /// Gets the definition with the given name, or nullptr if there is no such definition.
    /// If no definition is found an appropriate diagnostic will be issued.
    DefinitionLookupResult getDefinition(std::string_view name, const Scope& scope,
                                         SourceRange sourceRange, DiagCode code) const;

    /// Gets the definition indicated by the given config rule, or nullptr if it does not exist.
    /// If no definition is found an appropriate diagnostic will be issued.
    DefinitionLookupResult getDefinition(std::string_view name, const Scope& scope,
                                         const ConfigRule& configRule, SourceRange sourceRange,
                                         DiagCode code) const;

    /// Gets the definition indicated by the given bind directive info.
    DefinitionLookupResult getDefinition(std::string_view name, const Scope& scope,
                                         SourceRange sourceRange,
                                         const BindDirectiveInfo& bindInfo) const;

    /// Gets the definition for the given syntax node, or nullptr if it does not exist.
    const DefinitionSymbol* getDefinition(const Scope& scope,
                                          const syntax::ModuleDeclarationSyntax& syntax) const;

    /// Gets the definition indicated by the given config and cell ID, or nullptr
    /// if it does not exist. If no definition is found an appropriate diagnostic will be issued.
    const DefinitionSymbol* getDefinition(const ConfigBlockSymbol& config,
                                          std::string_view cellName, std::string_view libName,
                                          SourceRange sourceRange) const;

    /// Gets a list of all definitions (including primitives) in the design.
    std::vector<const Symbol*> getDefinitions() const;

    /// Gets the package with the give name, or nullptr if there is no such package.
    const PackageSymbol* getPackage(std::string_view name) const;

    /// Gets the built-in 'std' package.
    const PackageSymbol& getStdPackage() const { return *stdPkg; }

    /// Gets a list of all packages in the design.
    std::vector<const PackageSymbol*> getPackages() const;

    /// Gets the built-in gate type with the given name, or nullptr if there is no such gate.
    const PrimitiveSymbol* getGateType(std::string_view name) const;

    /// @}
    /// @name System function management
    /// @{

    /// Registers a system subroutine handler, which can be accessed by compiled code.
    void addSystemSubroutine(const std::shared_ptr<SystemSubroutine>& subroutine);

    /// Registers a type-based system method handler, which can be accessed by compiled code.
    void addSystemMethod(SymbolKind typeKind, const std::shared_ptr<SystemSubroutine>& method);

    /// Gets a system subroutine with the given name, or nullptr if there is no such subroutine
    /// registered.
    const SystemSubroutine* getSystemSubroutine(std::string_view name) const;

    /// Gets a system method for the specified type with the given name, or nullptr if there
    /// is no such method registered.
    const SystemSubroutine* getSystemMethod(SymbolKind typeKind, std::string_view name) const;

    /// Gets the attributes associated with the given symbol.
    std::span<const AttributeSymbol* const> getAttributes(const Symbol& symbol) const;

    /// Gets the attributes associated with the given statement.
    std::span<const AttributeSymbol* const> getAttributes(const Statement& stmt) const;

    /// Gets the attributes associated with the given expression.
    std::span<const AttributeSymbol* const> getAttributes(const Expression& expr) const;

    /// Gets the attributes associated with the given port connection.
    std::span<const AttributeSymbol* const> getAttributes(const PortConnection& conn) const;

    /// @}
    /// @name Internal AST construction
    /// @{

    /// Creates a new definition in the given scope based on the given syntax.
    void createDefinition(const Scope& scope, LookupLocation location,
                          const syntax::ModuleDeclarationSyntax& syntax);

    /// Creates a new package in the given scope based on the given syntax.
    const PackageSymbol& createPackage(const Scope& scope,
                                       const syntax::ModuleDeclarationSyntax& syntax);

    /// Creates a new config block in the given scope based on the given syntax.
    const ConfigBlockSymbol& createConfigBlock(const Scope& scope,
                                               const syntax::ConfigDeclarationSyntax& syntax);

    /// Creates a new primitive in the given scope based on the given syntax.
    const PrimitiveSymbol& createPrimitive(Scope& scope,
                                           const syntax::UdpDeclarationSyntax& syntax);

    /// Registers a built-in gate symbol.
    void addGateType(const PrimitiveSymbol& primitive);

    /// Sets the attributes associated with the given symbol.
    void setAttributes(const Symbol& symbol, std::span<const AttributeSymbol* const> attributes);

    /// Sets the attributes associated with the given statement.
    void setAttributes(const Statement& stmt, std::span<const AttributeSymbol* const> attributes);

    /// Sets the attributes associated with the given expression.
    void setAttributes(const Expression& expr, std::span<const AttributeSymbol* const> attributes);

    /// Sets the attributes associated with the given port connection.
    void setAttributes(const PortConnection& conn,
                       std::span<const AttributeSymbol* const> attributes);

    /// Notes the presence of a bind directive. These can be later checked during
    /// scope elaboration to include the newly bound instances.
    void noteBindDirective(const syntax::BindDirectiveSyntax& syntax, const Scope& scope);

    /// Notes an instance that contains a bind directive targeting a global definition.
    /// These are later checked for correctness.
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
        const Scope& scope, std::string_view className, std::string_view declName) const;

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

    /// Notes the existence of an extern module/interface/program/primitive declaration.
    void noteExternDefinition(const Scope& scope, const syntax::SyntaxNode& syntax);

    /// Performs a lookup for an extern module/interface/program/primitive declaration
    /// of the given name.
    const syntax::SyntaxNode* getExternDefinition(std::string_view name, const Scope& scope) const;

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

    /// Makes note of an alias defined between the bit ranges of the two given symbols.
    /// This is used to check for duplicate aliases between the bit ranges.
    void noteNetAlias(const Scope& scope, const Symbol& firstSym, DriverBitRange firstRange,
                      const Expression& firstExpr, const Symbol& secondSym,
                      DriverBitRange secondRange, const Expression& secondExpr);

    /// Notes the existence of the given hierarchical reference, which is used,
    /// among other things, to ensure we perform instance caching correctly.
    void noteHierarchicalReference(const Scope& scope, const HierarchicalReference& ref);

    /// Notes the existence of a virtual interface type declaration for the given instance.
    void noteVirtualIfaceInstance(const InstanceSymbol& instance);

    /// Adds a set of diagnostics to the compilation's list of semantic diagnostics.
    void addDiagnostics(const Diagnostics& diagnostics);

    /// Forces the given symbol and all scopes underneath it to
    /// be elaborated and any relevant diagnostics to be issued.
    void forceElaborate(const Symbol& symbol);

    /// Gets the default time scale to use when none is specified in the source code.
    std::optional<TimeScale> getDefaultTimeScale() const { return options.defaultTimeScale; }

    /// Gets the next system ID to use for identifying enum types.
    int getNextEnumSystemId() { return nextEnumSystemId++; }

    /// Gets the next system ID to use for identifying struct types.
    int getNextStructSystemId() { return nextStructSystemId++; }

    /// Gets the next system ID to use for identifying union types.
    int getNextUnionSystemId() { return nextUnionSystemId++; }

    /// @}
    /// @name Types
    /// @{

    /// Gets the type associated with the given syntax node kind.
    /// If the syntax kind doesn't represent a type this will return the error type.
    const Type& getType(syntax::SyntaxKind kind) const;

    /// Gets the type represented by the given data type syntax node.
    const Type& getType(const syntax::DataTypeSyntax& node, const ASTContext& context,
                        const Type* typedefTarget = nullptr);

    /// Gets an array type created from the given element type and dimensions.
    const Type& getType(const Type& elementType,
                        const syntax::SyntaxList<syntax::VariableDimensionSyntax>& dimensions,
                        const ASTContext& context);

    /// Gets an integral vector type with the given size and flags.
    const Type& getType(bitwidth_t width, bitmask<IntegralFlags> flags);

    /// Gets a scalar (single bit) type with the given flags.
    const Type& getScalarType(bitmask<IntegralFlags> flags);

    /// Gets the nettype represented by the given token kind.
    /// If the token kind does not represent a nettype this will return the
    /// error nettype.
    const NetType& getNetType(parsing::TokenKind kind) const;

    /// Get the built-in `bit` type.
    const Type& getBitType() const { return *bitType; }

    /// Get the built-in `logic` type.
    const Type& getLogicType() const { return *logicType; }

    /// Get the built-in `int` type.
    const Type& getIntType() const { return *intType; }

    /// Get the built-in `byte` type.
    const Type& getByteType() const { return *byteType; }

    /// Get the built-in `integer` type.
    const Type& getIntegerType() const { return *integerType; }

    /// Get the built-in `real` type.
    const Type& getRealType() const { return *realType; }

    /// Get the built-in `shortreal` type.
    const Type& getShortRealType() const { return *shortRealType; }

    /// Get the built-in `string` type.
    const Type& getStringType() const { return *stringType; }

    /// Get the built-in `void` type.
    const Type& getVoidType() const { return *voidType; }

    /// Get the error type, which is used as a placeholder
    /// to represent an invalid type.
    const Type& getErrorType() const { return *errorType; }

    /// Get the built-in `int unsigned` type.
    const Type& getUnsignedIntType();

    /// Get the built-in `null` type.
    const Type& getNullType();

    /// Get the built-in `$` type.
    const Type& getUnboundedType();

    /// Get the built-in type used for the result of the `type()` operator.
    const Type& getTypeRefType();

    /// Get the `wire` built in net type. The rest of the built-in net types are
    /// rare enough that we don't bother providing dedicated accessors for them.
    const NetType& getWireNetType() const { return *wireNetType; }

    /// @}
    /// @name Allocation functions
    /// @{

    /// Allocates space for a constant value in the pool of constants.
    ConstantValue* allocConstant(ConstantValue&& value) {
        return constantAllocator.emplace(std::move(value));
    }

    /// Allocates a symbol map.
    SymbolMap* allocSymbolMap() { return symbolMapAllocator.emplace(); }

    /// Allocates a pointer map.
    PointerMap* allocPointerMap() { return pointerMapAllocator.emplace(); }

    /// Allocates an assertion instance details object.
    AssertionInstanceDetails* allocAssertionDetails();

    /// Allocates a generic class symbol.
    template<typename... Args>
    GenericClassDefSymbol* allocGenericClass(Args&&... args) {
        return genericClassAllocator.emplace(std::forward<Args>(args)...);
    }

    /// Allocates a config block symbol.
    ConfigBlockSymbol* allocConfigBlock(std::string_view name, SourceLocation loc);

    /// Allocates a scope's wildcard import data object.
    Scope::WildcardImportData* allocWildcardImportData();

    /// Gets the driver map allocator.
    DriverIntervalMap::allocator_type& getDriverMapAllocator() { return driverMapAllocator; }

    /// Gets the unroll interval map allocator.
    UnrollIntervalMap::allocator_type& getUnrollIntervalMapAllocator() {
        return unrollIntervalMapAllocator;
    }

    /// Creates an empty ImplicitTypeSyntax object.
    const syntax::ImplicitTypeSyntax& createEmptyTypeSyntax(SourceLocation loc);

    /// @}

private:
    friend class Lookup;
    friend class Scope;
    friend struct DiagnosticVisitor;

    // Collected information about a resolved bind directive.
    struct ResolvedBind {
        SmallVector<const Symbol*> instTargets;
        DefinitionLookupResult instanceDef;
        const DefinitionSymbol* defTarget = nullptr;
        const ResolvedConfig* resolvedConfig = nullptr;
    };

    // These functions are called by Scopes to create and track various members.
    Scope::DeferredMemberData& getOrAddDeferredData(Scope::DeferredMemberIndex& index);

    bool doTypoCorrection() const { return typoCorrections < options.typoCorrectionLimit; }
    void didTypoCorrection() { typoCorrections++; }

    std::span<const AttributeSymbol* const> getAttributes(const void* ptr) const;

    Diagnostic& addDiag(Diagnostic diag);

    const RootSymbol& getRoot(bool skipDefParamsAndBinds);
    void elaborate();
    void insertDefinition(Symbol& symbol, const Scope& scope);
    void parseParamOverrides(flat_hash_map<std::string_view, const ConstantValue*>& results);
    void checkDPIMethods(std::span<const SubroutineSymbol* const> dpiImports);
    void checkExternIfaceMethods(std::span<const MethodPrototypeSymbol* const> protos);
    void checkModportExports(
        std::span<const std::pair<const InterfacePortSymbol*, const ModportSymbol*>> modports);
    void checkElemTimeScale(std::optional<TimeScale> timeScale, SourceRange sourceRange);
    void resolveDefParamsAndBinds();
    void resolveBindTargets(const syntax::BindDirectiveSyntax& syntax, const Scope& scope,
                            ResolvedBind& resolvedBind);
    void checkBindTargetParams(const syntax::BindDirectiveSyntax& syntax, const Scope& scope,
                               const ResolvedBind& resolvedBind);
    void checkVirtualIfaceInstance(const InstanceSymbol& instance);
    std::pair<DefinitionLookupResult, bool> resolveConfigRule(const Scope& scope,
                                                              const ConfigRule& rule) const;
    std::pair<DefinitionLookupResult, bool> resolveConfigRules(
        std::string_view name, const Scope& scope, const ResolvedConfig* parentConfig,
        const ConfigRule* configRule, const std::vector<Symbol*>& defList) const;
    Diagnostic* errorMissingDef(std::string_view name, const Scope& scope, SourceRange sourceRange,
                                DiagCode code) const;

    // Stored options object.
    CompilationOptions options;

    // Specialized allocators for types that are not trivially destructible.
    TypedBumpAllocator<SymbolMap> symbolMapAllocator;
    TypedBumpAllocator<PointerMap> pointerMapAllocator;
    TypedBumpAllocator<ConstantValue> constantAllocator;
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

    // A map of syntax nodes that have been referenced in the AST.
    // The value indicates whether the node has been used as an lvalue vs non-lvalue,
    // for things like variables and nets.
    flat_hash_map<const syntax::SyntaxNode*, std::pair<bool, bool>> referenceStatusMap;

    // The name map for all module, interface, program, and primitive definitions.
    // The key is a combination of definition name + the scope in which it was declared.
    // The value is a pair -- the first element is a list of definitions that share
    // the given name / scope (which can happen for multiple libraries at the root scope),
    // and the second element is a boolean that indicates whether there exists at least
    // one nested module with the given name (requiring a more involved lookup).
    flat_hash_map<std::tuple<std::string_view, const Scope*>, std::pair<std::vector<Symbol*>, bool>>
        definitionMap;

    // A cache of vector types, keyed on various properties such as bit width.
    flat_hash_map<uint32_t, const Type*> vectorTypeCache;

    // Map from syntax kinds to the built-in types.
    flat_hash_map<syntax::SyntaxKind, const Type*> knownTypes;

    // Map from token kinds to the built-in net types.
    flat_hash_map<parsing::TokenKind, std::unique_ptr<NetType>> knownNetTypes;

    // The name map for packages. Note that packages have their own namespace,
    // which is why they can't share the definitions name table.
    flat_hash_map<std::string_view, const PackageSymbol*> packageMap;

    // The name map for system subroutines.
    flat_hash_map<std::string_view, std::shared_ptr<SystemSubroutine>> subroutineMap;

    // The name map for system methods.
    flat_hash_map<std::tuple<std::string_view, SymbolKind>, std::shared_ptr<SystemSubroutine>>
        methodMap;

    // Map from pointers (to symbols, statements, expressions) to their associated attributes.
    flat_hash_map<const void*, std::span<const AttributeSymbol* const>> attributeMap;

    // Map from instance bodies to hierarchical references that extend up through them.
    flat_hash_map<const Symbol*, std::vector<const HierarchicalReference*>> hierRefMap;

    struct SyntaxMetadata {
        const syntax::SyntaxTree* tree = nullptr;
        const NetType* defaultNetType = nullptr;
        std::optional<TimeScale> timeScale;
        UnconnectedDrive unconnectedDrive = UnconnectedDrive::None;
    };

    // Map from syntax nodes to parse-time metadata about them.
    flat_hash_map<const syntax::SyntaxNode*, SyntaxMetadata> syntaxMetadata;

    // A list of all created definitions, as storage for their memory.
    std::vector<std::unique_ptr<DefinitionSymbol>> definitionMemory;

    // A map from diag code + location to the diagnostics that have occurred at that location.
    // This is used to collapse duplicate diagnostics across instantiations into a single report.
    using DiagMap = flat_hash_map<std::tuple<DiagCode, SourceLocation>, std::vector<Diagnostic>>;
    DiagMap diagMap;

    // A list of libraries that control the order in which we search for cell bindings.
    std::vector<const SourceLibrary*> defaultLiblist;

    // A list of instances that have been created by virtual interface type declarations.
    std::vector<const InstanceSymbol*> virtualInterfaceInstances;

    // A map from class name + decl name + scope to out-of-block declarations. These get
    // registered when we find the initial declaration and later get used when we see
    // the class prototype. The value also includes a boolean indicating whether anything
    // has used this declaration -- an error is issued if it's never used.
    mutable flat_hash_map<
        std::tuple<std::string_view, std::string_view, const Scope*>,
        std::tuple<const syntax::SyntaxNode*, const syntax::ScopedNameSyntax*, SymbolIndex, bool>>
        outOfBlockDecls;

    std::unique_ptr<RootSymbol> root;
    const SourceManager* sourceManager = nullptr;
    size_t numErrors = 0; // total number of errors inserted into the diagMap
    bool finalized = false;
    bool finalizing = false; // to prevent reentrant calls to getRoot()
    bool anyElemsWithTimescales = false;
    bool diagsDisabled = false;
    uint32_t typoCorrections = 0;
    int nextEnumSystemId = 1;
    int nextStructSystemId = 1;
    int nextUnionSystemId = 1;

    TypedBumpAllocator<GenericClassDefSymbol> genericClassAllocator;
    TypedBumpAllocator<AssertionInstanceDetails> assertionDetailsAllocator;
    TypedBumpAllocator<ConfigBlockSymbol> configBlockAllocator;
    TypedBumpAllocator<Scope::WildcardImportData> wildcardImportAllocator;

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
    std::vector<const DefinitionSymbol*> unreferencedDefs;

    // The name map for built-in primitive definitions. These are stored in a separate
    // map because they are distinguished by keyword names that may otherwise collide
    // with escaped identifiers used by user code.
    flat_hash_map<std::string_view, const PrimitiveSymbol*> gateMap;

    // A map from syntax node to the definition it represents. Used much less frequently
    // than other ways of looking up definitions which is why it's lower down here.
    flat_hash_map<const syntax::ModuleDeclarationSyntax*, std::vector<DefinitionSymbol*>>
        definitionFromSyntax;

    // A set of all instantiated names in the design; used for determining whether a given
    // module has ever been instantiated to know whether it should be considered top-level.
    flat_hash_set<std::string_view> globalInstantiations;

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

    // A map of config blocks.
    flat_hash_map<std::string_view, std::vector<const ConfigBlockSymbol*>> configBlocks;
    flat_hash_map<const syntax::SyntaxNode*, const ConfigBlockSymbol*> configBySyntax;

    // A map of library names to their actual source library pointers.
    flat_hash_map<std::string_view, const SourceLibrary*> libraryNameMap;

    // A set of instances that have global definition-based bind directives applied.
    // This is pretty rare and only used for checking of type params.
    flat_hash_map<const DefinitionSymbol*, std::vector<const Symbol*>> instancesWithDefBinds;

    // The name map for extern module/interface/program/primitive declarations.
    // The key is a combination of definition name + the scope in which it was declared.
    flat_hash_map<std::tuple<std::string_view, const Scope*>, const syntax::SyntaxNode*>
        externDefMap;

    struct NetAlias {
        const Symbol* sym;
        DriverBitRange range;
        const Expression* firstExpr;
        const Expression* secondExpr;
    };

    using AliasIntervalMap = IntervalMap<uint64_t, const NetAlias*>;
    AliasIntervalMap::allocator_type netAliasAllocator;

    // A map of net aliases to check for duplicates. For any given alias the key is
    // whichever symbol has the lower address in memory.
    flat_hash_map<const Symbol*, AliasIntervalMap> netAliases;

    // The built-in std package.
    const PackageSymbol* stdPkg = nullptr;

    // The default library.
    std::unique_ptr<SourceLibrary> defaultLibMem;
    const SourceLibrary* defaultLibPtr;
};

} // namespace slang::ast
