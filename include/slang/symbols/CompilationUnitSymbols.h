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

class ModuleInstanceSymbol;
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

/// A SystemVerilog package construct.
class PackageSymbol : public Symbol, public Scope {
public:
    const NetType& defaultNetType;
    TimeScale timeScale;

    PackageSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                  const NetType& defaultNetType);

    void serializeTo(ASTSerializer&) const {}

    static PackageSymbol& fromSyntax(Compilation& compilation,
                                     const ModuleDeclarationSyntax& syntax, const Scope& scope);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Package; }
};

/// Represents the entirety of a design, along with all contained compilation units.
class RootSymbol : public Symbol, public Scope {
public:
    span<const ModuleInstanceSymbol* const> topInstances;
    span<const CompilationUnitSymbol* const> compilationUnits;

    explicit RootSymbol(Compilation& compilation) :
        Symbol(SymbolKind::Root, "$root", SourceLocation()), Scope(compilation, this) {}

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Root; }
};

} // namespace slang