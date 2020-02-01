//------------------------------------------------------------------------------
//! @file CompilationUnitSymbols.h
//! @brief Contains compilation unit-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/Scope.h"
#include "slang/symbols/Symbol.h"
#include "slang/symbols/TimeScaleSymbolBase.h"

namespace slang {

class ModuleInstanceSymbol;

/// The root of a single compilation unit.
class CompilationUnitSymbol : public Symbol, public Scope, TimeScaleSymbolBase {
public:
    explicit CompilationUnitSymbol(Compilation& compilation);

    void addMembers(const SyntaxNode& syntax);

    TimeScale getTimeScale() const { return timeScale; }
    void toJson(json&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CompilationUnit; }

private:
    // Used for tracking whether a time scale directive is first in scope.
    bool anyMembers = false;
};

/// A SystemVerilog package construct.
class PackageSymbol : public Symbol, public Scope, TimeScaleSymbolBase {
public:
    const NetType& defaultNetType;

    PackageSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                  const NetType& defaultNetType);

    TimeScale getTimeScale() const { return timeScale; }
    void toJson(json&) const {}

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

    void toJson(json&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::Root; }
};

} // namespace slang