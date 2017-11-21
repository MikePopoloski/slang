//------------------------------------------------------------------------------
// RootSymbol.h
// Root symbol definition.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "Symbol.h"
#include "SymbolFactory.h"

namespace slang {

/// Represents the entirety of a design, along with all contained compilation units.
class RootSymbol : public ScopeSymbol {
public:
    explicit RootSymbol(const SourceManager& sourceManager);
    explicit RootSymbol(const SyntaxTree* tree);
    explicit RootSymbol(span<const SyntaxTree* const> trees);
    RootSymbol(const SourceManager& sourceManager, span<const CompilationUnitSyntax* const> units);

    /// Gets all of the compilation units in the design.
    span<const CompilationUnitSymbol* const> compilationUnits() const { return unitList; }

    /// Finds all of the top-level module instances in the design. These form the roots of the
    /// actual design hierarchy.
    span<const ModuleInstanceSymbol* const> topInstances() const { return topList; }

    /// Finds a package in the design with the given name, or returns null if none is found.
    const PackageSymbol* findPackage(string_view name) const;

    /// Report an error at the specified location.
    Diagnostic& addError(DiagCode code, SourceLocation location_) const {
        return diags.add(code, location_);
    }

    /// Allocate an object using the design's shared allocator.
    template<typename T, typename... Args>
    T& allocate(Args&&... args) const {
        return *alloc.emplace<T>(std::forward<Args>(args)...);
    }

    BumpAllocator& allocator() const { return alloc; }
    Diagnostics& diagnostics() const { return diags; }
    const SourceManager& sourceManager() const { return sourceMan; }

    // TODO: clean this up
    mutable TypedBumpAllocator<ConstantValue> constantAllocator;

    mutable SymbolFactory factory;

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
    SymbolMap packageMap;

    // list of compilation units in the design
    std::vector<const CompilationUnitSymbol*> unitList;

    // These are mutable so that the design root can be logically const, observing
    // members lazily but allocating them on demand and reporting errors when asked.
    mutable BumpAllocator alloc;
    mutable Diagnostics diags;

    // list of top level module instances in the design
    std::vector<ModuleInstanceSymbol*> topList;

    const SourceManager& sourceMan;
};

}