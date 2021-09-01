//------------------------------------------------------------------------------
//! @file Scope.h
//! @brief Base class for symbols that represent lexical scopes
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>

#include "slang/binding/Lookup.h"
#include "slang/diagnostics/Diagnostics.h"
#include "slang/symbols/SemanticFacts.h"
#include "slang/symbols/Symbol.h"
#include "slang/util/Iterator.h"
#include "slang/util/Util.h"

namespace slang {

class BindContext;
class Compilation;
class ForwardingTypedefSymbol;
class InstanceBodySymbol;
class NetType;
class WildcardImportSymbol;
struct AttributeInstanceSyntax;
struct NameSyntax;
struct PackageImportItemSyntax;
struct PortConnectionSyntax;
struct PortDeclarationSyntax;

using SymbolMap = flat_hash_map<string_view, const Symbol*>;
using PointerMap = flat_hash_map<uintptr_t, uintptr_t>;

/// Base class for symbols that represent a name scope; that is, they contain children and can
/// participate in name lookup.
class Scope {
public:
    /// Adds a symbol as a member to the scope.
    void addMember(const Symbol& symbol);

    /// Creates and adds one or more member symbols to the scope from the given syntax node.
    void addMembers(const SyntaxNode& syntax);

    const Symbol& asSymbol() const { return *thisSym; }

    /// Gets the compilation that contains this scope.
    Compilation& getCompilation() const { return compilation; }

    /// Gets the default net type for implicit nets in this scope.
    const NetType& getDefaultNetType() const;

    /// Gets the time scale for delay values expressed within this scope.
    TimeScale getTimeScale() const;

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
    const Symbol* find(string_view name) const;

    /// Finds a direct child member with the given name. This won't return anything weird like
    /// forwarding typedefs or imported symbols, but will return things like transparent enum
    /// members. This method expects that the symbol will be found and be of the given type `T`.
    template<typename T>
    const T& find(string_view name) const {
        const Symbol* sym = find(name);
        ASSERT(sym);
        return sym->as<T>();
    }

    /// Performs a full fledged name lookup starting in the current scope, following all
    /// SystemVerilog rules for qualified or unqualified name resolution. The name to look up
    /// is parsed from the given input string.
    const Symbol* lookupName(string_view name, LookupLocation location = LookupLocation::max,
                             bitmask<LookupFlags> flags = LookupFlags::None) const;

    /// Performs a full fledged name lookup starting in the current scope, following all
    /// SystemVerilog rules for qualified or unqualified name resolution. The name to look up
    /// is parsed from the given input string. This method expects that the symbol will be found and
    /// be of the given type `T`.
    template<typename T>
    const T& lookupName(string_view name, LookupLocation location = LookupLocation::max,
                        bitmask<LookupFlags> flags = LookupFlags::None) const {
        const Symbol* sym = lookupName(name, location, flags);
        ASSERT(sym);
        return sym->as<T>();
    }

    /// Gets a specific member at the given zero-based index, expecting it to be of
    /// the specified type. This expects (and asserts) that the member at the given
    /// index is of the specified type `T`.
    template<typename T>
    const T& memberAt(uint32_t index) const {
        return std::next(members().begin(), index)->as<T>();
    }

    /// An iterator for members in the scope.
    class iterator : public iterator_facade<iterator, std::forward_iterator_tag, const Symbol> {
    public:
        iterator() : current(nullptr) {}
        iterator(const Symbol* firstSymbol) : current(firstSymbol) {}
        iterator(const iterator& other) : current(other.current) {}

        iterator& operator=(const iterator& other) {
            current = other.current;
            return *this;
        }

        bool operator==(const iterator& other) const { return current == other.current; }

        const Symbol& operator*() const { return *current; }
        const Symbol& operator*() { return *current; }

        iterator& operator++();

        iterator operator++(int) {
            iterator tmp = *this;
            ++(*this);
            return tmp;
        }

    private:
        const Symbol* current;
    };

    template<typename SpecificType>
    class specific_symbol_iterator
        : public iterator_facade<specific_symbol_iterator<SpecificType>, std::forward_iterator_tag,
                                 const SpecificType> {
    public:
        specific_symbol_iterator() : current(nullptr) {}
        specific_symbol_iterator(const Symbol* firstSymbol) : current(firstSymbol) { skipToNext(); }
        specific_symbol_iterator(const specific_symbol_iterator& other) : current(other.current) {}

        specific_symbol_iterator& operator=(const specific_symbol_iterator& other) {
            current = other.current;
            return *this;
        }

        bool operator==(const specific_symbol_iterator& other) const {
            return current == other.current;
        }

        const SpecificType& operator*() const { return current->as<SpecificType>(); }
        const SpecificType& operator*() { return current->as<SpecificType>(); }

        specific_symbol_iterator& operator++() {
            current = current->nextInScope;
            skipToNext();
            return *this;
        }

        specific_symbol_iterator operator++(int) {
            specific_symbol_iterator tmp = *this;
            ++(*this);
            return tmp;
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

    /// Gets an iterator to the members contained in the scope.
    iterator_range<iterator> members() const {
        ensureElaborated();
        return { firstMember, nullptr };
    }

    /// Gets an iterator to all of the members of the given type contained in the scope.
    template<typename T>
    iterator_range<specific_symbol_iterator<T>> membersOfType() const {
        ensureElaborated();
        return { firstMember, nullptr };
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

    span<const WildcardImportSymbol* const> getWildcardImports() const;

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
        span<Symbol* const> getMembers() const;

        using TransparentTypeMap = flat_hash_map<const Symbol*, const Symbol*>;
        void registerTransparentType(const Symbol* insertion, const Symbol& parent);
        iterator_range<TransparentTypeMap::const_iterator> getTransparentTypes() const;

        void addForwardingTypedef(const ForwardingTypedefSymbol& symbol);
        span<const ForwardingTypedefSymbol* const> getForwardingTypedefs() const;

        void addPortDeclaration(const PortDeclarationSyntax& syntax, const Symbol* insertion);
        span<std::pair<const PortDeclarationSyntax*, const Symbol*> const> getPortDeclarations()
            const;

        void addNameConflict(const Symbol& member);
        span<const Symbol* const> getNameConflicts() const;

    private:
        // A list of deferred member symbols.
        std::vector<Symbol*> members;

        // Some types are special in that their members leak into the surrounding scope; this
        // set keeps track of all variables, parameters, arguments, etc that have such data types
        // so that when our list of members is finalized we can include their members as well.
        TransparentTypeMap transparentTypes;

        // Track a list of forwarding typedefs declared in the scope; once we've fully elaborated
        // we'll go back and make sure they're actually valid.
        std::vector<const ForwardingTypedefSymbol*> forwardingTypedefs;

        // Track a list of non-ANSI port declarations declared in the scope; once we've fully
        // elaborated we'll go back and make sure they're valid.
        std::vector<std::pair<const PortDeclarationSyntax*, const Symbol*>> portDecls;

        // A list of members that have name conflicts that need to be reported.
        std::vector<const Symbol*> nameConflicts;
    };

    // Sideband collection of wildcard imports stored in the Compilation object.
    using ImportData = std::vector<const WildcardImportSymbol*>;

    // Inserts the given member symbol into our own list of members, right after
    // the given symbol. If `at` is null, it will insert at the head of the list.
    void insertMember(const Symbol* member, const Symbol* at, bool isElaborating,
                      bool incrementIndex) const;

    // Gets or creates deferred member data in the Compilation object's sideband table.
    DeferredMemberData& getOrAddDeferredData() const;

    // Elaborates all deferred members and then releases the entry from the
    // Compilation object's sideband table.
    void elaborate() const;

    // Handles name conflicts between symbols in the scope.
    void handleNameConflict(const Symbol& member, const Symbol*& existing,
                            bool isElaborating) const;

    // Reports an error for a name conflict between two symbols.
    void reportNameConflict(const Symbol& member, const Symbol& existing) const;

    // Checks for a conflict when multiple imports (or exports) target symbols
    // with the same name.
    void checkImportConflict(const Symbol& member, const Symbol& existing) const;

    // Add a wildcard import to this scope.
    void addWildcardImport(const PackageImportItemSyntax& item,
                           span<const AttributeInstanceSyntax* const> attributes);

    // Helper for adding in one or more deferred members from a syntax node.
    void addDeferredMembers(const SyntaxNode& syntax);

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
    mutable DeferredMemberIndex deferredMemberIndex{ 0 };

    // If this scope has any wildcard import directives we'll keep track of them
    // in a sideband list in the compilation object.
    ImportDataIndex importDataIndex{ 0 };
};

} // namespace slang
