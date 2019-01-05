//------------------------------------------------------------------------------
// Scope.h
// Base class for symbols that represent lexical scopes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>

#include "slang/symbols/Symbol.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/Iterator.h"
#include "slang/util/Util.h"

namespace slang {

class Compilation;
class ForwardingTypedefSymbol;
class Scope;
class StatementBodiedScope;
class SystemSubroutine;
class WildcardImportSymbol;

using SymbolMap = flat_hash_map<string_view, const Symbol*>;

/// Additional modifiers for a lookup operation.
enum class LookupFlags {
    /// No special modifiers.
    None = 0,

    /// The lookup is occurring in a constant context. This adds an additional
    /// restriction that the symbols cannot be referenced by hierarchical path.
    Constant = 1,

    /// A lookup for a type name, as opposed to a value. These names cannot be hierarchical
    /// but can be package or class scoped.
    Type = 2,

    /// Usually lookups require that the found symbol be declared before the lookup
    /// location. This flag removes that restriction.
    AllowDeclaredAfter = 4,

    /// Allow the lookup to return a system subroutine instead of a normal symbol.
    AllowSystemSubroutine = 8,

    /// Don't search through wildcard imports to satisfy the lookup.
    DisallowWildcardImport = 16
};
BITMASK_DEFINE_MAX_ELEMENT(LookupFlags, DisallowWildcardImport);

/// This type denotes the ordering of symbols within a particular scope, for the purposes of
/// determining whether a found symbol is visible compared to the given location.
/// For example, variables cannot be referenced before they are declared.
class LookupLocation {
public:
    LookupLocation() = default;

    /// Places a location just before the given symbol in its parent scope.
    static LookupLocation before(const Symbol& symbol);

    /// Places a location just after the given symbol in its parent scope.
    static LookupLocation after(const Symbol& symbol);

    /// A special location that should always compare after any other.
    static const LookupLocation max;

    /// A special location that should always compare before any other.
    static const LookupLocation min;

    bool operator==(const LookupLocation& other) const {
        return scope == other.scope && index == other.index;
    }

    bool operator!=(const LookupLocation& other) const { return !(*this == other); }
    bool operator<(const LookupLocation& other) const;

private:
    friend class Scope;

    LookupLocation(const Scope* scope_, uint32_t index) : scope(scope_), index(index) {}

    const Scope* scope = nullptr;
    uint32_t index = 0;
};

struct LookupResult {
    const Symbol* found = nullptr;
    const SystemSubroutine* systemSubroutine = nullptr;
    bool wasImported = false;
    bool isHierarchical = false;

    struct MemberSelector {
        string_view name;
        SourceLocation dotLocation;
        SourceRange nameRange;
    };

    using Selector = std::variant<const ElementSelectSyntax*, MemberSelector>;
    SmallVectorSized<Selector, 4> selectors;

    Diagnostic& addDiag(const Scope& scope, DiagCode code, SourceLocation location);
    Diagnostic& addDiag(const Scope& scope, DiagCode code, SourceRange sourceRange);

    const Diagnostics& getDiagnostics() const { return diagnostics; }

    bool hasError() const;
    void clear();
    void copyFrom(const LookupResult& other);

private:
    Diagnostics diagnostics;
};

/// Base class for symbols that represent a name scope; that is, they contain children and can
/// participate in name lookup.
class Scope {
public:
    /// Adds a symbol as a member to the scope.
    void addMember(const Symbol& symbol);

    /// Creates and adds one or more member symbols to the scope from the given syntax node.
    void addMembers(const SyntaxNode& syntax);

    /// Gets the parent scope of this scope.
    const Scope* getParent() const;
    const Symbol& asSymbol() const { return *thisSym; }

    /// Gets the compilation that contains this scope.
    Compilation& getCompilation() const { return compilation; }

    Diagnostic& addDiag(DiagCode code, SourceLocation location) const;
    Diagnostic& addDiag(DiagCode code, SourceRange sourceRange) const;

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
    /// SystemVerilog rules for qualified or unqualified name resolution.
    void lookupName(const NameSyntax& syntax, LookupLocation location, bitmask<LookupFlags> flags,
                    LookupResult& result) const;

    /// Performs a full fledged name lookup starting in the current scope, following all
    /// SystemVerilog rules for qualified or unqualified name resolution. The name to look up
    /// is parsed from the given input string.
    const Symbol* lookupName(string_view name, LookupLocation location = LookupLocation::max,
                             bitmask<LookupFlags> flags = LookupFlags::None) const;

    /// Performs an unqualified lookup in this scope, then recursively up the parent
    /// chain until we reach root or the symbol is found.
    const Symbol* lookupUnqualifiedName(string_view name, LookupLocation location,
                                        SourceRange sourceRange,
                                        bitmask<LookupFlags> flags = LookupFlags::None) const;

    /// Gets a specific member at the given zero-based index, expecting it to be of the specified
    /// type. This expects (and asserts) that the member at the given index is of the specified type
    /// `T`.
    template<typename T>
    const T& memberAt(uint32_t index) const {
        return std::next(members().begin(), index)->as<T>();
    }

    /// An iterator for members in the scope.
    class iterator : public iterator_facade<iterator, std::forward_iterator_tag, const Symbol> {
    public:
        iterator(const Symbol* firstSymbol) : current(firstSymbol) {}

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
        specific_symbol_iterator(const Symbol* firstSymbol) : current(firstSymbol) { skipToNext(); }

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

protected:
    Scope(Compilation& compilation_, const Symbol* thisSym_);

    /// Before we access any members to do lookups or return iterators, make sure
    /// the scope is fully elaborated.
    void ensureElaborated() const {
        if (deferredMemberIndex != DeferredMemberIndex::Invalid)
            elaborate();
    }

    void setStatement(StatementBodiedScope& stmt) { getOrAddDeferredData().setStatement(stmt); }

    void setPortConnections(const SeparatedSyntaxList<PortConnectionSyntax>& connections) {
        getOrAddDeferredData().setPortConnections(connections);
    }

    const Symbol* getLastMember() const { return lastMember; }

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

        bool hasStatement() const;
        void setStatement(StatementBodiedScope& stmt);
        StatementBodiedScope* getStatement() const;

        void setPortConnections(const SeparatedSyntaxList<PortConnectionSyntax>& connections);
        const SeparatedSyntaxList<PortConnectionSyntax>* getPortConnections() const {
            return portConns;
        }

        using TransparentTypeMap = flat_hash_map<const Symbol*, const Symbol*>;
        void registerTransparentType(const Symbol* insertion, const Symbol& parent);
        iterator_range<TransparentTypeMap::const_iterator> getTransparentTypes() const;

        void addForwardingTypedef(const ForwardingTypedefSymbol& symbol);
        span<const ForwardingTypedefSymbol* const> getForwardingTypedefs() const;

        void addPortDeclaration(const PortDeclarationSyntax& syntax);
        span<const PortDeclarationSyntax* const> getPortDeclarations() const;

    private:
        // A given scope only ever stores one of the following:
        // - A list of syntax nodes that represent deferred members that need to be elaborated
        //   before any lookups or iterations are done of members in the scope.
        // - A StatementBodiedScope.
        std::variant<std::vector<Symbol*>, StatementBodiedScope*> membersOrStatement;

        // Some types are special in that their members leak into the surrounding scope; this
        // set keeps track of all variables, parameters, arguments, etc that have such data types
        // so that when our list of members is finalized we can include their members as well.
        TransparentTypeMap transparentTypes;

        // Track a list of forwarding typedefs declared in the scope; once we've fully elaborated
        // we'll go back and make sure they're actually valid.
        std::vector<const ForwardingTypedefSymbol*> forwardingTypedefs;

        // Track a list of non-ANSI port declarations declared in the scope; once we've fully
        // elaborated we'll go back and make sure they're valid.
        std::vector<const PortDeclarationSyntax*> portDecls;

        // For instances, track port connections.
        const SeparatedSyntaxList<PortConnectionSyntax>* portConns = nullptr;
    };

    // Sideband collection of wildcard imports stored in the Compilation object.
    using ImportData = std::vector<const WildcardImportSymbol*>;

    // Inserts the given member symbol into our own list of members, right after
    // the given symbol. If `at` is null, it will insert at the head of the list.
    void insertMember(const Symbol* member, const Symbol* at) const;

    // Gets or creates deferred member data in the Compilation object's sideband table.
    DeferredMemberData& getOrAddDeferredData();

    // Elaborates all deferred members and then releases the entry from the
    // Compilation object's sideband table.
    void elaborate() const;

    // Performs an unqualified lookup in this scope, then recursively up the parent
    // chain until we reach root or the symbol is found.
    void lookupUnqualifiedImpl(string_view name, LookupLocation location, SourceRange sourceRange,
                               bitmask<LookupFlags> flags, LookupResult& result) const;

    // Performs a qualified lookup in this scope using all of the various language rules for name
    // resolution.
    void lookupQualified(const ScopedNameSyntax& syntax, LookupLocation location,
                         bitmask<LookupFlags> flags, LookupResult& result) const;

    // Reports an error for an undeclared identifier.
    void reportUndeclared(string_view name, SourceRange range, bitmask<LookupFlags> flags,
                          LookupResult& result) const;

    // Gets the index of a new symbol inserted after the given symbol within this scope.
    Symbol::Index getInsertionIndex(const Symbol& at) const;

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
