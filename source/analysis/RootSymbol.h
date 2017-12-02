//------------------------------------------------------------------------------
// RootSymbol.h
// Root symbol definition.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <unordered_set>

#include "Compilation.h"
#include "Symbol.h"

namespace slang {

/// Represents the entirety of a design, along with all contained compilation units.
class RootSymbol : public Symbol, public Scope {
public:
    RootSymbol();
    explicit RootSymbol(const SyntaxTree* tree);
    explicit RootSymbol(span<const SyntaxTree* const> trees);
    explicit RootSymbol(span<const CompilationUnitSyntax* const> units);

    /// Gets all of the compilation units in the design.
    span<const CompilationUnitSymbol* const> compilationUnits() const { return unitList; }

    /// Finds all of the top-level module instances in the design. These form the roots of the
    /// actual design hierarchy.
    span<const ModuleInstanceSymbol* const> topInstances() const { return topList; }

    /// Finds a package in the design with the given name, or returns null if none is found.
    const PackageSymbol* findPackage(string_view name) const;

    mutable Compilation compilation;

private:
    // Initializes the list of members from the given set of roots; called by several constructors.
    void init(span<const SyntaxNode* const> nodes);

    SubroutineSymbol& createSystemFunction(string_view name, SystemFunction kind,
                                           std::initializer_list<const TypeSymbol*> argTypes) const;

    // These functions are used for traversing the syntax hierarchy and finding all instantiations.
    using NameSet = std::unordered_set<string_view>;
    static void findInstantiations(const ModuleDeclarationSyntax& module, std::vector<NameSet>& scopeStack,
                                   NameSet& found);
    static void findInstantiations(const MemberSyntax& node, std::vector<NameSet>& scopeStack, NameSet& found);

    // The name map for packages. Note that packages have their own namespace,
    // which is why they can't share the root name table.
    flat_hash_map<string_view, const Symbol*> packageMap;

    // list of compilation units in the design
    std::vector<const CompilationUnitSymbol*> unitList;

    // list of top level module instances in the design
    std::vector<ModuleInstanceSymbol*> topList;
};

}
