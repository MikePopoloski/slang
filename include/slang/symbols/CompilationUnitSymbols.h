//------------------------------------------------------------------------------
//! @file CompilationUnitSymbols.h
//! @brief Contains compilation unit-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"

namespace slang {

class InstanceSymbol;
struct ModuleDeclarationSyntax;

/// The root of a single compilation unit.
class CompilationUnitSymbol : public Symbol, public Scope {
public:
    TimeScale timeScale;

    explicit CompilationUnitSymbol(Compilation& compilation);

    void addMembers(const SyntaxNode& syntax);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CompilationUnit; }

private:
    // Used for tracking whether a time scale directive is first in scope.
    bool anyMembers = false;
    optional<SourceRange> unitsRange;
    optional<SourceRange> precisionRange;
};

struct PackageImportItemSyntax;

/// A SystemVerilog package construct.
class PackageSymbol : public Symbol, public Scope {
public:
    const NetType& defaultNetType;
    TimeScale timeScale;
    VariableLifetime defaultLifetime;
    span<const PackageImportItemSyntax* const> exportDecls;
    bool hasExportAll = false;

    PackageSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                  const NetType& defaultNetType, VariableLifetime defaultLifetime);

    /// Searches for a symbol by name, in the context of importing from the package.
    /// This is similar to a call to find() but also includes symbols that have been
    /// exported from the package.
    const Symbol* findForImport(string_view name) const;

    /// Notes that the given symbol was imported into this package from some other package.
    void noteImport(const Symbol& symbol) const;

    void serializeTo(ASTSerializer&) const {}

    static PackageSymbol& fromSyntax(const Scope& scope, const ModuleDeclarationSyntax& syntax,
                                     const NetType& defaultNetType,
                                     optional<TimeScale> directiveTimeScale);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Package; }

private:
    mutable bool hasForceElaborated = false;
};

/// Represents the entirety of a design, along with all contained compilation units.
class RootSymbol : public Symbol, public Scope {
public:
    span<const InstanceSymbol* const> topInstances;
    span<const CompilationUnitSymbol* const> compilationUnits;

    explicit RootSymbol(Compilation& compilation) :
        Symbol(SymbolKind::Root, "$root", SourceLocation()), Scope(compilation, this) {}

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Root; }
};

} // namespace slang
