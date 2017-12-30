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

using SymbolList = span<const Symbol* const>;
using SymbolMap = flat_hash_map<string_view, const Symbol*>;

/// Specifies possible kinds of lookups that can be done.
enum class LookupNameKind {
    /// A lookup of a simple name, starting in the local scope. The lookup location is
    /// used to qualify accessible signals. Imports from packages are considered.
    Local,

    /// The lookup is for the first part of a scoped name. This first performs
    /// the equivalent of a Local lookup; if no symbol is found using that method,
    /// it will search for a package with the given name.
    Scoped,

    /// A lookup for a simple name that is part of a callable expression (task or function).
    /// This has additional rules; specifically, SystemVerilog allows tasks and functions
    /// to be referenced before they are declared.
    Callable,

    /// Names referenced as part of a bind instantiation have special rules. For example,
    /// previously imported wildcard names are visible, but the bind lookup itself will
    /// not cause non-imported wildcard names to become visible even if they match.
    BindTarget
};

/// This type denotes the ordering of symbols within a particular scope,
/// for the purposes of determining whether a found symbol is visible
/// compared to the given reference point. For example, variables cannot
/// be referenced before they are declared.
class LookupRefPoint {
public:
    LookupRefPoint() = default;

    /// Places a reference point just before the given symbol in its parent scope.
    static LookupRefPoint before(const Symbol& symbol);

    /// Places a reference point just after the given symbol in its parent scope.
    static LookupRefPoint after(const Symbol& symbol);

    /// Places a reference point at the start of the given scope.
    static LookupRefPoint startOfScope(const Scope& scope);

    /// Places a reference point at the end of the given scope.
    static LookupRefPoint endOfScope(const Scope& scope);

    /// A special reference point that should always compare after any other reference point.
    static const LookupRefPoint max;

    /// A special reference point that should always compare before any other reference point.
    static const LookupRefPoint min;

    bool operator==(const LookupRefPoint& other) const {
        return scope == other.scope && index == other.index;
    }

    bool operator!=(const LookupRefPoint& other) const { return !(*this == other); }
    bool operator<(const LookupRefPoint& other) const;

private:
    friend class Scope;

    LookupRefPoint(const Scope* scope_, uint32_t index) :
        scope(scope_), index(index) {}

    const Scope* scope = nullptr;
    uint32_t index = 0;
};

/// A container for various lookup options and storage for the results of the operation.
class LookupResult {
public:
    LookupResult() { clear(); }

    /// Specifies possible kinds of results that can occur from a lookup.
    enum LookupResultKind {
        /// A single good symbol was found.
        Found,

        /// No symbols at all were found.
        NotFound,

        /// A symbol was found but it was inaccessible given the reference point.
        UsedBeforeDeclared,

        /// More than one symbol was found in imported packages; the results are ambiguous.
        AmbiguousImport,

        /// The lookup would cause a name to be imported into a scope that already has
        /// a symbol with that name. @a getFoundSymbol will return the conflicting local
        /// symbol and the import statement that brought in the other symbol will be listed
        /// in the potential imports list.
        ImportNameConflict
    };

    /// The kind of name lookup to be performed.
    LookupNameKind nameKind;

    /// The reference point by which found symbols will be qualified. This is used, for example,
    /// to ensure that variables aren't used before they are declared.
    LookupRefPoint referencePoint;

    /// Gets the kind of result that occurred.
    LookupResultKind getResultKind() const { return resultKind; }

    /// Gets the single found symbol, or null if no viable symbol was found.
    const Symbol* getFoundSymbol() const { return symbol; }

    /// Gets a list of potentially viable import statements; this indicates
    /// which imports were responsible for an ambiguous import result.
    SymbolList getPotentialImports() const { return imports; }

    /// Indicates whether the found symbol was actually imported from a package somewhere.
    bool wasImported() const { return resultWasImported; }

    /// Indicates whether the kind of name lookup being performed relies on knowing
    /// the lookup reference point.
    bool referencePointMatters() const {
        return nameKind == LookupNameKind::Local || nameKind == LookupNameKind::Scoped;
    }

    /// Issues diagnostics corresponding to the results of the lookup, if any.
    void diagnose(SourceLocation location, Diagnostics& diagnostics);

    /// Clears the result object and resets all state to the defaults.
    void clear();

    /// Sets the symbol that was found as the result of successful lookup.
    void setSymbol(const Symbol& symbol, bool wasImported = false);

    /// Adds an import symbol from which the looked up name is visible.
    void addPotentialImport(const Symbol& import);

    //void setUsedBeforeDeclared(const Symbol& symbol);
    //void setImportConflict(const Symbol& localSymbol, const Symbol& import);

private:
    SmallVectorSized<const Symbol*, 2> imports;
    LookupResultKind resultKind;
    const Symbol* symbol;
    bool resultWasImported;
};

/// Base class for scopes that can contain child symbols and look them up by name.
class Scope {
public:
    void addMember(const Symbol& symbol);
    void addMembers(const SyntaxNode& syntax);

    const Scope* getParent() const;
    const Symbol& asSymbol() const { return *thisSym; }
    Compilation& getCompilation() const { return compilation; }

    /// Performs a symbol lookup using SystemVerilog name lookup rules.
    ///
    /// @param searchName the unqualified name for which to search.
    /// @param result an object that will contain the results of the search.
    ///
    void lookup(string_view searchName, LookupResult& result) const;

    /// Performs a direct lookup of a name within the current scope. Returns null if no
    /// symbol is found. This will not look into parent scopes and does not care about
    /// from where you are performing the lookup.
    const Symbol* lookupDirect(string_view searchName) const;

    /// Performs a direct lookup of a symbol in the current scope, expecting it to exist
    /// and be of the given type. If those conditions do not hold, this will assert.
    template<typename T>
    const T& lookupDirect(string_view name) const {
        const Symbol* sym = lookupDirect(name);
        ASSERT(sym);
        return sym->as<T>();
    }

    /// Gets a specific member at the given zero-based index, expecting it to be of the specified type.
    /// If the type does not match, this will assert.
    template<typename T>
    const T& memberAt(uint32_t index) const { return (*std::next(members().begin(), index))->as<T>(); }

    /// A helper method to evaluate a constant in the current scope.
    //ConstantValue evaluateConstant(const ExpressionSyntax& expr) const;

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

        const SpecificType* operator*() const { return &current->template as<SpecificType>(); }
        const SpecificType* operator*() { return &current->template as<SpecificType>(); }

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