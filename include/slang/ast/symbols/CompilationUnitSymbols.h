//------------------------------------------------------------------------------
//! @file CompilationUnitSymbols.h
//! @brief Contains compilation unit-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Compilation.h"
#include "slang/ast/Scope.h"
#include "slang/ast/Symbol.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::syntax {
class SyntaxTree;
}

namespace slang::ast {

class ConfigBlockSymbol;
class Expression;
class InstanceSymbol;
class Type;

/// The root of a single compilation unit.
class SLANG_EXPORT CompilationUnitSymbol : public Symbol, public Scope {
public:
    std::optional<TimeScale> timeScale;
    const SourceLibrary& sourceLibrary;

    CompilationUnitSymbol(Compilation& compilation, const SourceLibrary& sourceLibrary);

    void addMembers(const syntax::SyntaxNode& syntax);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CompilationUnit; }

private:
    // Used for tracking whether a time scale directive is first in scope.
    bool anyMembers = false;
    std::optional<SourceRange> unitsRange;
    std::optional<SourceRange> precisionRange;
};

/// A SystemVerilog package construct.
class SLANG_EXPORT PackageSymbol : public Symbol, public Scope {
public:
    const NetType& defaultNetType;
    std::optional<TimeScale> timeScale;
    VariableLifetime defaultLifetime;
    std::span<const syntax::PackageImportItemSyntax* const> exportDecls;
    bool hasExportAll = false;

    PackageSymbol(Compilation& compilation, std::string_view name, SourceLocation loc,
                  const NetType& defaultNetType, VariableLifetime defaultLifetime);

    /// Searches for a symbol by name, in the context of importing from the package.
    /// This is similar to a call to find() but also includes symbols that have been
    /// exported from the package.
    const Symbol* findForImport(std::string_view name) const;

    void serializeTo(ASTSerializer&) const {}

    static PackageSymbol& fromSyntax(const Scope& scope,
                                     const syntax::ModuleDeclarationSyntax& syntax,
                                     const NetType& defaultNetType,
                                     std::optional<TimeScale> directiveTimeScale);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Package; }
};

/// Represents the entirety of a design, along with all contained compilation units.
class SLANG_EXPORT RootSymbol : public Symbol, public Scope {
public:
    std::span<const InstanceSymbol* const> topInstances;
    std::span<const CompilationUnitSymbol* const> compilationUnits;

    explicit RootSymbol(Compilation& compilation) :
        Symbol(SymbolKind::Root, "$root", SourceLocation()), Scope(compilation, this) {}

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Root; }
};

/// Represents a module, interface, or program definition.
class SLANG_EXPORT DefinitionSymbol : public Symbol {
public:
    /// Information about a single parameter declaration.
    struct ParameterDecl {
        union {
            const syntax::ParameterDeclarationSyntax* valueSyntax;
            const syntax::TypeParameterDeclarationSyntax* typeSyntax;
            const Type* givenType;
        };

        union {
            const syntax::DeclaratorSyntax* valueDecl;
            const syntax::TypeAssignmentSyntax* typeDecl;
            const Expression* givenInitializer;
        };

        /// The name of the parameter.
        std::string_view name;

        /// The source location where the parameter is defined.
        SourceLocation location;

        /// Attributes associated with the parameter.
        std::span<const syntax::AttributeInstanceSyntax* const> attributes;

        /// True if this is a type parameter.
        bool isTypeParam;

        /// True if this is a localparam.
        bool isLocalParam;

        /// True if this parameter is declared in the definition's port list.
        bool isPortParam;

        /// True if there is a syntax node associated with this parameter. This controls
        /// which members of the unions are valid.
        bool hasSyntax;

        /// Constructs a new ParameterDecl instance.
        ParameterDecl(const Scope& scope, const syntax::ParameterDeclarationSyntax& syntax,
                      const syntax::DeclaratorSyntax& decl, bool isLocal, bool isPort,
                      std::span<const syntax::AttributeInstanceSyntax* const> attributes);

        /// Constructs a new ParameterDecl instance.
        ParameterDecl(const Scope& scope, const syntax::TypeParameterDeclarationSyntax& syntax,
                      const syntax::TypeAssignmentSyntax& decl, bool isLocal, bool isPort,
                      std::span<const syntax::AttributeInstanceSyntax* const> attributes);

        /// Constructs a new ParameterDecl instance.
        ParameterDecl(std::string_view name, SourceLocation location, const Type& givenType,
                      bool isLocal, bool isPort, const Expression* givenInitializer);

        /// Constructs a new ParameterDecl instance.
        ParameterDecl(std::string_view name, SourceLocation location, bool isLocal, bool isPort,
                      const Type* defaultType);

        /// Indicates whether this parameter has a default value expression.
        bool hasDefault() const;
    };

    /// The default nettype for implicit nets within this definition.
    const NetType& defaultNetType;

    /// The kind of definition (module, interface, or program).
    DefinitionKind definitionKind;

    /// The default lifetime for variables declared within this definition.
    VariableLifetime defaultLifetime;

    /// The drive setting to use for unconnected nets within this definition.
    UnconnectedDrive unconnectedDrive;

    /// The timescale specified for this definition, or nullopt if none
    /// is explicitly specified.
    std::optional<TimeScale> timeScale;

    /// A list of parameters declared by this definition.
    SmallVector<ParameterDecl, 8> parameters;

    /// A list of ports declared by this definition.
    const syntax::PortListSyntax* portList;

    /// A set of modport names declared by this definition.
    flat_hash_set<std::string_view> modports;

    /// A set of bind directives that apply to all instances of this definition.
    std::vector<BindDirectiveInfo> bindDirectives;

    /// The syntax tree that contains this definition, or nullptr if constructed
    /// outside of any specific syntax tree.
    const syntax::SyntaxTree* syntaxTree;

    /// The source library that contains the definition.
    const SourceLibrary& sourceLibrary;

    /// Indicates whether this definition has non-ansi port declarations.
    bool hasNonAnsiPorts;

    /// Constructs a new instance of the DefinitionSymbol class.
    DefinitionSymbol(const Scope& scope, LookupLocation lookupLocation,
                     const syntax::ModuleDeclarationSyntax& syntax, const NetType& defaultNetType,
                     UnconnectedDrive unconnectedDrive, std::optional<TimeScale> directiveTimeScale,
                     const syntax::SyntaxTree* syntaxTree);

    /// Returns a string description of the definition kind, such as "module",
    /// "interface", or "program".
    std::string_view getKindString() const;

    /// Returns a string description of the definition kind, including an
    /// indefinite article. e.g. "a module", "an interface".
    std::string_view getArticleKindString() const;

    /// Returns the number of times the definition has been instantiated so far
    /// in the visited design.
    size_t getInstanceCount() const { return instanceCount; }

    /// Notes that the definition has been instantiated.
    void noteInstantiated() const { instanceCount++; }

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Definition; }

private:
    mutable size_t instanceCount = 0;
};

/// A rule that controls how a specific cell or instance in the design is configured.
struct SLANG_EXPORT ConfigRule {
    /// A list of libraries to use to look up definitions.
    std::optional<std::span<const SourceLibrary* const>> liblist;

    /// Contains information about how to look up a specific cell for this rule.
    struct CellId {
        /// The library containing the cell (or empty to specify
        /// that other logic should be used to find the library).
        std::string_view lib;

        /// The name of the cell.
        std::string_view name;

        /// The source range where this cell id was declared.
        SourceRange sourceRange;

        /// If true, this ID targets a config block specifically.
        bool targetConfig = false;
    };

    /// A specific cell to use for this instance or definition lookup.
    CellId useCell;

    /// Parameter overrides to apply to the instance.
    const syntax::ParameterValueAssignmentSyntax* paramOverrides = nullptr;

    /// The syntax node that created this config rule.
    not_null<const syntax::SyntaxNode*> syntax;

    /// A flag that marks whether this rule has been used during elaboration.
    mutable bool isUsed = false;

    explicit ConfigRule(const syntax::SyntaxNode& syntax) : syntax(&syntax) {}
};

/// Contains information about a resolved configuration rule
/// that affects an instance and the hierarchy underneath it.
struct SLANG_EXPORT ResolvedConfig {
    /// A specific configuration to use for this hierarchy.
    const ConfigBlockSymbol& useConfig;

    /// The root instance of this particular configuration hierarchy.
    const InstanceSymbol& rootInstance;

    /// A list of libraries to use to look up definitions.
    std::span<const SourceLibrary* const> liblist;

    /// The original rule that led to this resolved configuration.
    const ConfigRule* configRule = nullptr;

    ResolvedConfig(const ConfigBlockSymbol& useConfig, const InstanceSymbol& rootInstance);
};

/// Represents a config block declaration.
class SLANG_EXPORT ConfigBlockSymbol : public Symbol, public Scope {
public:
    struct TopCell {
        const DefinitionSymbol& definition;
        ConfigRule* rule = nullptr;
        SourceRange sourceRange;

        TopCell(const DefinitionSymbol& definition, SourceRange sourceRange) :
            definition(definition), sourceRange(sourceRange) {}
    };

    struct CellOverride {
        flat_hash_map<const SourceLibrary*, ConfigRule*> specificLibRules;
        ConfigRule* defaultRule = nullptr;
    };

    struct InstanceOverride {
        flat_hash_map<std::string_view, InstanceOverride> childNodes;
        ConfigRule* rule = nullptr;
    };

    /// A flag that marks whether this config block has been used during elaboration.
    mutable bool isUsed = false;

    ConfigBlockSymbol(Compilation& compilation, std::string_view name, SourceLocation loc) :
        Symbol(SymbolKind::ConfigBlock, name, loc), Scope(compilation, this) {}

    std::span<const TopCell> getTopCells() const {
        if (!resolved)
            resolve();
        return topCells;
    }

    std::span<const SourceLibrary* const> getDefaultLiblist() const {
        if (!resolved)
            resolve();
        return defaultLiblist;
    }

    const flat_hash_map<std::string_view, CellOverride>& getCellOverrides() const {
        if (!resolved)
            resolve();
        return cellOverrides;
    }

    const flat_hash_map<std::string_view, InstanceOverride>& getInstanceOverrides() const {
        if (!resolved)
            resolve();
        return instanceOverrides;
    }

    const ConfigRule* findRuleFromSyntax(const syntax::SyntaxNode& syntax) const;

    void checkUnusedRules() const;

    static ConfigBlockSymbol& fromSyntax(const Scope& scope,
                                         const syntax::ConfigDeclarationSyntax& syntax);

    void serializeTo(ASTSerializer& serialize) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ConfigBlock; }

private:
    void resolve() const;
    void registerRules(const InstanceOverride& node) const;

    mutable std::span<const TopCell> topCells;
    mutable std::span<const SourceLibrary* const> defaultLiblist;
    mutable flat_hash_map<std::string_view, CellOverride> cellOverrides;
    mutable flat_hash_map<std::string_view, InstanceOverride> instanceOverrides;
    mutable flat_hash_map<const syntax::SyntaxNode*, const ConfigRule*> ruleBySyntax;
    mutable bool resolved = false;
};

} // namespace slang::ast
