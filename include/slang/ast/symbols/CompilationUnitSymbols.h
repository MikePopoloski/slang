//------------------------------------------------------------------------------
//! @file CompilationUnitSymbols.h
//! @brief Contains compilation unit-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Scope.h"
#include "slang/ast/Symbol.h"
#include "slang/syntax/SyntaxFwd.h"

namespace slang::syntax {
class SyntaxTree;
}

namespace slang::ast {

class Expression;
class InstanceSymbol;
class Type;

/// The root of a single compilation unit.
class SLANG_EXPORT CompilationUnitSymbol : public Symbol, public Scope {
public:
    std::optional<TimeScale> timeScale;

    explicit CompilationUnitSymbol(Compilation& compilation);

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

    /// Notes that the given symbol was imported into this package from some other package.
    void noteImport(const Symbol& symbol) const;

    void serializeTo(ASTSerializer&) const {}

    static PackageSymbol& fromSyntax(const Scope& scope,
                                     const syntax::ModuleDeclarationSyntax& syntax,
                                     const NetType& defaultNetType,
                                     std::optional<TimeScale> directiveTimeScale);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Package; }

private:
    mutable bool hasForceElaborated = false;
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
    std::vector<const syntax::BindDirectiveSyntax*> bindDirectives;

    /// The syntax tree that contains this definition, or nullptr if constructed
    /// outside of any specific syntax tree.
    const syntax::SyntaxTree* syntaxTree;

    /// The source library that contains the definition, or nullptr for the
    /// default library.
    const SourceLibrary* sourceLibrary;

    /// Indicates whether this definition has non-ansi port declarations.
    bool hasNonAnsiPorts;

    /// Constructs a new instance of the DefinitionSymbol class.
    DefinitionSymbol(const Scope& scope, LookupLocation lookupLocation,
                     const syntax::ModuleDeclarationSyntax& syntax, const NetType& defaultNetType,
                     UnconnectedDrive unconnectedDrive, std::optional<TimeScale> directiveTimeScale,
                     const syntax::SyntaxTree* syntaxTree, const SourceLibrary* sourceLibrary);

    /// Returns a string description of the definition kind, such as "module",
    /// "interface", or "program".
    std::string_view getKindString() const;

    /// Returns a string description of the definition kind, including an
    /// indefinite article. e.g. "a module", "an interface".
    std::string_view getArticleKindString() const;

    /// Returns true if the definition has been instantiated anywhere in the design.
    bool isInstantiated() const { return instantiated; }

    /// Notes that the definition has been instantiated.
    void noteInstantiated() const { instantiated = true; }

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Definition; }

private:
    mutable bool instantiated = false;
};

/// Identifies a specific cell as part of a config rule.
struct ConfigCellId {
    /// The library containing the cell (or empty to specify
    /// that other logic should be used to find the library).
    std::string_view lib;

    /// The name of the cell.
    std::string_view name;

    /// The source range where this cell id was declared.
    SourceRange sourceRange;

    ConfigCellId() = default;
    ConfigCellId(std::string_view lib, std::string_view name, SourceRange sourceRange) :
        lib(lib), name(name), sourceRange(sourceRange) {}
};

/// A rule that controls how a specific cell or instance in the design is configured.
struct ConfigRule {
    /// A list of libraries to use to look up definitions.
    std::span<const SourceLibrary* const> liblist;

    /// A specific cell to use for this instance or definition lookup.
    ConfigCellId useCell;
};

/// Represents a config block declaration.
class SLANG_EXPORT ConfigBlockSymbol : public Symbol, public Scope {
public:
    struct CellOverride {
        const SourceLibrary* specificLib = nullptr;
        ConfigRule rule;
    };

    struct InstanceOverride {
        std::span<const std::string_view> path;
        ConfigRule rule;
    };

    const SourceLibrary* sourceLibrary = nullptr;
    std::span<const ConfigCellId> topCells;
    std::span<const SourceLibrary* const> defaultLiblist;
    std::span<const InstanceOverride> instanceOverrides;
    flat_hash_map<std::string_view, std::vector<CellOverride>> cellOverrides;

    ConfigBlockSymbol(Compilation& compilation, std::string_view name, SourceLocation loc) :
        Symbol(SymbolKind::ConfigBlock, name, loc), Scope(compilation, this) {}

    static ConfigBlockSymbol& fromSyntax(const Scope& scope,
                                         const syntax::ConfigDeclarationSyntax& syntax);

    void serializeTo(ASTSerializer& serialize) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ConfigBlock; }
};

} // namespace slang::ast
