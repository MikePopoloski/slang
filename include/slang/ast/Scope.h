//------------------------------------------------------------------------------
//! @file Scope.h
//! @brief Base class for symbols that represent lexical scopes
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include <ranges>

#include "slang/ast/Lookup.h"
#include "slang/ast/SemanticFacts.h"
#include "slang/ast/Symbol.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/util/Hash.h"
#include "slang/util/Iterator.h"
#include "slang/util/Util.h"

namespace slang::syntax {

class SyntaxNode;

} // namespace slang::syntax

namespace slang::ast {

class ASTContext;
class Compilation;
class ForwardingTypedefSymbol;
class InstanceBodySymbol;
class NetType;
class WildcardImportSymbol;

using SymbolMap = flat_hash_map<std::string_view, const Symbol*>;
using PointerMap = flat_hash_map<uintptr_t, uintptr_t>;

/// Base class for symbols that represent a name scope; that is, they contain children and can
/// participate in name lookup.
class SLANG_EXPORT Scope {
public:
    Scope(const Scope&) = delete;
    Scope& operator=(const Scope&) = delete;

    /// Adds a symbol as a member to the scope.
    void addMember(const Symbol& symbol);

    /// Creates and adds one or more member symbols to the scope from the given syntax node.
    void addMembers(const syntax::SyntaxNode& syntax);

    const Symbol& asSymbol() const { return *thisSym; }

    /// Gets the compilation that contains this scope.
    Compilation& getCompilation() const { return compilation; }

    /// Gets the default net type for implicit nets in this scope.
    const NetType& getDefaultNetType() const;

    /// Gets the time scale for delay values expressed within this scope.
    std::optional<TimeScale> getTimeScale() const;

    /// Returns true if this scope represents a procedural context; that is,
    /// a procedural block, or a task/function scope.
    bool isProceduralContext() const;

    /// Gets the instance body that contains this scope, if applicable.
    /// Otherwise returns nullptr.
    const InstanceBodySymbol* getContainingInstance() const;

    /// Returns true if this scope is in an uninstantiated context, like if
    /// in a module that is not used in the design.
    bool isUninstantiated() const;

    Diagnostic& addDiag(DiagCode code, SourceLocation location) const;
    Diagnostic& addDiag(DiagCode code, SourceRange sourceRange) const;
    void addDiags(const Diagnostics& diags) const;

    /// Finds a direct child member with the given name. This won't return anything weird like
    /// forwarding typedefs or imported symbols, but will return things like transparent enum
    /// members. If no symbol is found with the given name, nullptr is returned.
    const Symbol* find(std::string_view name) const;

    /// Finds a direct child member with the given name. This won't return anything weird like
    /// forwarding typedefs or imported symbols, but will return things like transparent enum
    /// members. This method expects that the symbol will be found and be of the given type `T`.
    template<typename T>
    const T& find(std::string_view name) const {
        const Symbol* sym = find(name);
        SLANG_ASSERT(sym);
        return sym->as<T>();
    }

    /// Performs a full fledged name lookup starting in the current scope, following all
    /// SystemVerilog rules for qualified or unqualified name resolution. The name to look up
    /// is parsed from the given input string.
    const Symbol* lookupName(std::string_view name, LookupLocation location = LookupLocation::max,
                             bitmask<LookupFlags> flags = LookupFlags::None) const;

    /// Performs a full fledged name lookup starting in the current scope, following all
    /// SystemVerilog rules for qualified or unqualified name resolution. The name to look up
    /// is parsed from the given input string. This method expects that the symbol will be found and
    /// be of the given type `T`.
    template<typename T>
    const T& lookupName(std::string_view name, LookupLocation location = LookupLocation::max,
                        bitmask<LookupFlags> flags = LookupFlags::None) const {
        const Symbol* sym = lookupName(name, location, flags);
        SLANG_ASSERT(sym);
        return sym->as<T>();
    }

    /// Gets a specific member at the given zero-based index, expecting it to be of
    /// the specified type. This expects (and asserts) that the member at the given
    /// index is of the specified type `T`.
    template<typename T>
    const T& memberAt(uint32_t index) const {
        return std::ranges::next(members().begin(), index)->as<T>();
    }

    /// An iterator for members in the scope.
    class iterator : public iterator_facade<iterator> {
    public:
        iterator() : current(nullptr) {}
        iterator(const Symbol* firstSymbol) : current(firstSymbol) {}

        const Symbol& dereference() const { return *current; }
        void increment() { current = current->nextInScope; }
        bool equals(const iterator& other) const { return current == other.current; }

    private:
        const Symbol* current;
    };

    template<typename SpecificType>
    class specific_symbol_iterator
        : public iterator_facade<specific_symbol_iterator<SpecificType>> {
    public:
        specific_symbol_iterator() : current(nullptr) {}
        specific_symbol_iterator(const Symbol* firstSymbol) : current(firstSymbol) { skipToNext(); }

        const SpecificType& dereference() const { return current->as<SpecificType>(); }

        void increment() {
            current = current->nextInScope;
            skipToNext();
        }

        bool equals(const specific_symbol_iterator& other) const {
            return current == other.current;
        }

    private:
        void skipToNext() {
            while (current && !SpecificType::isKind(current->kind))
                current = current->nextInScope;
        }

        const Symbol* current;
    };

    /// Checks whether the scope is empty (has no members).
    [[nodiscard]] bool empty() const {
        ensureElaborated();
        return firstMember == nullptr;
    }

    /// Gets the range of members contained in the scope.
    std::ranges::subrange<iterator> members() const {
        ensureElaborated();
        return {firstMember, nullptr};
    }

    /// Gets the range of members of the given type contained in the scope.
    template<typename T>
    std::ranges::subrange<specific_symbol_iterator<T>> membersOfType() const {
        ensureElaborated();
        return {firstMember, nullptr};
    }

    /// Gets a pointer to the first member in the scope. Note that this does not
    /// force elaboration of the scope.
    const Symbol* getFirstMember() const { return firstMember; }

    /// Gets a pointer to the last member in the scope. Note that this does not
    /// force elaboration of the scope.
    const Symbol* getLastMember() const { return lastMember; }

    const SymbolMap& getNameMap() const {
        ensureElaborated();
        return *nameMap;
    }

    const SymbolMap& getUnelaboratedNameMap() const { return *nameMap; }

    std::span<const WildcardImportSymbol* const> getWildcardImports() const;

protected:
    Scope(Compilation& compilation_, const Symbol* thisSym_);

    /// Before we access any members to do lookups or return iterators, make sure
    /// the scope is fully elaborated.
    void ensureElaborated() const {
        if (deferredMemberIndex != DeferredMemberIndex::Invalid)
            elaborate();
    }

    /// Flag the need for this scope to be elaborated before members are accessed.
    void setNeedElaboration() { getOrAddDeferredData(); }

    /// Add a preconstructed wildcard import to this scope.
    void addWildcardImport(const WildcardImportSymbol& item);

    void addDeferredMembers(const syntax::SyntaxNode& syntax);

private:
    friend class Compilation;

    // Strongly typed index type which is used in a sideband list in the Compilation object
    // to store information about deferred members in this scope.
    enum class DeferredMemberIndex : uint32_t { Invalid = 0 };

    // Strongly typed index type which is used in a sideband list in the Compilation object
    // to store information about wildcard imports in this scope.
    enum class ImportDataIndex : uint32_t { Invalid = 0 };

    // Data stored in sideband tables in the Compilation object for deferred members.
    class DeferredMemberData {
    public:
        void addMember(Symbol* symbol);
        std::span<Symbol* const> getMembers() const;

        void registerTransparentType(const Symbol* insertion, const Symbol& parent);
        std::span<std::pair<const Symbol*, const Symbol*> const> getTransparentTypes() const;

        void addForwardingTypedef(const ForwardingTypedefSymbol& symbol);
        std::span<const ForwardingTypedefSymbol* const> getForwardingTypedefs() const;

        void addPortDeclaration(const syntax::SyntaxNode& syntax, const Symbol* insertion);
        std::span<std::pair<const syntax::SyntaxNode*, const Symbol*> const> getPortDeclarations()
            const;

    private:
        // A list of deferred member symbols.
        std::vector<Symbol*> members;

        // Some types are special in that their members leak into the surrounding scope; this
        // set keeps track of all variables, parameters, arguments, etc that have such data types
        // so that when our list of members is finalized we can include their members as well.
        std::vector<std::pair<const Symbol*, const Symbol*>> transparentTypes;

        // Track a list of forwarding typedefs declared in the scope; once we've fully elaborated
        // we'll go back and make sure they're actually valid.
        std::vector<const ForwardingTypedefSymbol*> forwardingTypedefs;

        // Track a list of non-ANSI port declarations declared in the scope; once we've fully
        // elaborated we'll go back and make sure they're valid.
        std::vector<std::pair<const syntax::SyntaxNode*, const Symbol*>> portDecls;
    };

    // Sideband collection of wildcard imports stored in the Compilation object.
    using ImportData = std::vector<const WildcardImportSymbol*>;

    void insertMember(const Symbol* member, const Symbol* at, bool isElaborating,
                      bool incrementIndex) const;

    DeferredMemberData& getOrAddDeferredData() const;
    void elaborate() const;
    void handleNameConflict(const Symbol& member) const;
    void handleNameConflict(const Symbol& member, const Symbol*& existing,
                            bool isElaborating) const;
    bool handleDataDeclaration(const syntax::DataDeclarationSyntax& syntax);
    void handleUserDefinedNet(const syntax::UserDefinedNetDeclarationSyntax& syntax);
    void handleNestedDefinition(const syntax::ModuleDeclarationSyntax& syntax) const;
    void handleExportedMethods(std::span<Symbol* const> deferredMembers) const;
    void reportNameConflict(const Symbol& member, const Symbol& existing) const;
    void checkImportConflict(const Symbol& member, const Symbol& existing) const;
    void addWildcardImport(const syntax::PackageImportItemSyntax& item,
                           std::span<const syntax::AttributeInstanceSyntax* const> attributes);
    void tryFixupInstances(const syntax::DataDeclarationSyntax& syntax, const ASTContext& context,
                           SmallVectorBase<const Symbol*>& results) const;

    // The compilation that owns this scope.
    Compilation& compilation;

    // A pointer to the symbol that this scope represents.
    const Symbol* thisSym;

    // The map of names to members that can be looked up within this scope.
    SymbolMap* nameMap;

    // A linked list of member symbols in the scope. These are mutable because a
    // scope might have only deferred members, and realization of deferred members
    // happens in logically const scenarios (such as the first time a lookup is
    // performed in the scope).
    mutable const Symbol* firstMember = nullptr;
    mutable const Symbol* lastMember = nullptr;

    // If this scope has any deferred member symbols they'll be temporarily
    // stored in a sideband list in the compilation object until we expand them.
    mutable DeferredMemberIndex deferredMemberIndex{0};

    // If this scope has any wildcard import directives we'll keep track of them
    // in a sideband list in the compilation object.
    ImportDataIndex importDataIndex{0};
};

} // namespace slang::ast
