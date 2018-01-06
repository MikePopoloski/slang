//------------------------------------------------------------------------------
// Scope.h
// Base class for symbols that represent lexical scopes.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "flat_hash_map.hpp"

#include "symbols/Symbol.h"
#include "util/Iterator.h"

namespace slang {

class Compilation;
class Scope;
class SyntaxNode;
class WildcardImportSymbol;
struct LazyType;

using SymbolMap = flat_hash_map<string_view, const Symbol*>;

/// Base class for scopes that can contain child symbols and look them up by name.
class Scope {
public:
    void addMember(const Symbol& symbol);
    void addMembers(const SyntaxNode& syntax);

    const Scope* getParent() const;
    const Symbol& asSymbol() const { return *thisSym; }
    Compilation& getCompilation() const { return compilation; }

    const Symbol* find(string_view name) const;

    template<typename T>
    const T& find(string_view name) const {
        const Symbol* sym = find(name);
        ASSERT(sym);
        return sym->as<T>();
    }

    span<const WildcardImportSymbol* const> getImports() const;

    /// Gets a specific member at the given zero-based index, expecting it to be of the specified type.
    /// If the type does not match, this will assert.
    template<typename T>
    const T& memberAt(uint32_t index) const { return (*std::next(members().begin(), index))->as<T>(); }

    /// Strongly typed index type which is used in a sideband list in the Compilation object
    /// to store information about deferred members in this scope.
    enum class DeferredMemberIndex : uint32_t { Invalid = 0 };

    /// Data stored in sideband tables in the Compilation object for deferred members.
    class DeferredMemberData {
    public:
        void addMember(const SyntaxNode& member, const Symbol* insertionPoint) {
            std::get<0>(membersOrStatement).emplace_back(&member, insertionPoint);
        }

        span<std::tuple<const SyntaxNode*, const Symbol*> const> getMembers() const {
            return std::get<0>(membersOrStatement);
        }

        bool hasStatement() const { return membersOrStatement.index() == 1; }
        void setStatement(const SyntaxNode& syntax) { membersOrStatement = &syntax; }

        const SyntaxNode* getStatement() const {
            return std::get<1>(membersOrStatement);
        }

        void registerTransparentType(const Symbol* symbol, const LazyType& type) {
            transparentTypes.emplace(symbol, &type);
        }

        using TransparentTypeMap = flat_hash_map<const Symbol*, const LazyType*>;
        iterator_range<TransparentTypeMap::const_iterator> getTransparentTypes() const {
            return { transparentTypes.begin(), transparentTypes.end() };
        }

    private:
        // A given scope only ever stores one of the following:
        // - A list of syntax nodes that represent deferred members that need to be elaborated
        //   before any lookups or iterations are done of members in the scope.
        // - Statement syntax (a single node or a list of them) that describes the body
        //   of a StatementBodiedScope.
        std::variant<
            std::vector<std::tuple<const SyntaxNode*, const Symbol*>>,
            const SyntaxNode*
        > membersOrStatement;

        // Some types are special in that their members leak into the surrounding scope; this
        // set keeps track of all variables, parameters, arguments, etc that have such data types
        // so that when our list of members is finalized we can include their members as well.
        TransparentTypeMap transparentTypes;
    };

    /// Strongly typed index type which is used in a sideband list in the Compilation object
    /// to store information about wildcard imports in this scope.
    enum class ImportDataIndex : uint32_t { Invalid = 0 };

    /// Sideband collection of wildcard imports stored in the Compilation object.
    using ImportData = std::vector<const WildcardImportSymbol*>;

    /// An iterator for members in the scope.
    class iterator : public iterator_facade<iterator, std::forward_iterator_tag, const Symbol*> {
    public:
        iterator(const Symbol* firstSymbol) : current(firstSymbol) {}

        iterator& operator=(const iterator& other) {
            current = other.current;
            return *this;
        }

        bool operator==(const iterator& other) const { return current == other.current; }

        const Symbol* operator*() const { return current; }
        const Symbol* operator*() { return current; }

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
    class specific_symbol_iterator : public iterator_facade<specific_symbol_iterator<SpecificType>,
                                                            std::forward_iterator_tag,
                                                            const SpecificType*> {
    public:
        specific_symbol_iterator(const Symbol* firstSymbol) :
            current(firstSymbol)
        {
            skipToNext();
        }

        specific_symbol_iterator& operator=(const specific_symbol_iterator& other) {
            current = other.current;
            return *this;
        }

        bool operator==(const specific_symbol_iterator& other) const { return current == other.current; }

        const SpecificType* operator*() const { return &current->as<SpecificType>(); }
        const SpecificType* operator*() { return &current->as<SpecificType>(); }

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

    /// Gets the members contained in the scope.
    iterator_range<iterator> members() const {
        ensureMembers();
        return { firstMember, nullptr };
    }

    template<typename T>
    iterator_range<specific_symbol_iterator<T>> membersOfType() const {
        ensureMembers();
        return { firstMember, nullptr };
    }

protected:
    Scope(Compilation& compilation_, const Symbol* thisSym_);

    /// Before we access any members to do lookups or return iterators, make sure
    /// we don't have any deferred members to take care of first.
    void ensureMembers() const {
        if (deferredMemberIndex != DeferredMemberIndex::Invalid)
            realizeDeferredMembers();
    }

    /// Gets or creates deferred member data in the Compilation object's sideband table.
    DeferredMemberData& getOrAddDeferredData();

private:
    // Inserts the given member symbol into our own list of members, right after
    // the given symbol. If `at` is null, it will insert at the head of the list.
    void insertMember(const Symbol* member, const Symbol* at) const;

    // Adds a syntax node to the list of deferred members in the scope.
    void addDeferredMember(const SyntaxNode& member);

    // Elaborates all deferred members and then releases the entry from the
    // Compilation object's sideband table.
    void realizeDeferredMembers() const;

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
    mutable DeferredMemberIndex deferredMemberIndex {0};

    // If this scope has any wildcard import directives we'll keep track of them
    // in a sideband list in the compilation object.
    ImportDataIndex importDataIndex {0};
};

}