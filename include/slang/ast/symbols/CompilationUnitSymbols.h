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

namespace slang::ast {

class InstanceSymbol;

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
