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
#include "slang/util/FlatMap.h"
#include "slang/util/Iterator.h"
#include "slang/util/Util.h"

namespace slang::syntax {

class SyntaxNode;

} // namespace slang::syntax

namespace slang::ast {

class ASTContext;
class Compilation;
class CompilationUnitSymbol;
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
    void addMember(const Symbol& symbol) { insertMember(&symbol, lastMember, false, true); }

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

    /// Gets the instance body or checker body that contains this scope, if applicable.
    /// Otherwise returns nullptr.
    const Symbol* getContainingInstanceOrChecker() const;

    /// Gets the compilation unit that contains this scope, if applicable.
    /// Otherwise returns nullptr.
    const CompilationUnitSymbol* getCompilationUnit() const;

    /// Returns true if this scope is in an uninstantiated context, like if
    /// in a module that is not used in the design.
    bool isUninstantiated() const;

    /// Reports a new diagnostic under this scope.
    Diagnostic& addDiag(DiagCode code, SourceLocation location) const;

    /// Reports a new diagnostic under this scope.
    Diagnostic& addDiag(DiagCode code, SourceRange sourceRange) const;

    /// Reports the given set of diagnostics under this scope.
    void addDiags(const Diagnostics& diags) const;

    /// @brief Finds a direct child member with the given name.
    ///
    /// This won't return anything weird like forwarding typedefs or imported symbols,
    /// but will return things like transparent enum members. If no symbol is found with
    /// the given name, nullptr is returned.
    const Symbol* find(std::string_view name) const;

    /// @brief Finds a direct child member with the given name.
    ///
    /// This won't return anything weird like forwarding typedefs or imported symbols,
    /// but will return things like transparent enum members. This method asserts that
    /// the symbol is found and is of the given type `T`.
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
        /// Constructs a default iterator that points nowhere.
        iterator() : current(nullptr) {}

        /// Constructs an iterator pointing at the given child symbol in the scope.
        iterator(const Symbol* firstSymbol) : current(firstSymbol) {}

        /// Dereferences the iterator, resolving it to a symbol.
        const Symbol& dereference() const { return *current; }

        /// Advances the iterator to the next symbol in the scope.
        void increment() { current = current->nextInScope; }

        /// @returns true if the given iterator is equal to this one.
        bool equals(const iterator& other) const { return current == other.current; }

    private:
        const Symbol* current;
    };

    /// An iterator for members in the scope of the specified type.
    template<typename SpecificType>
    class specific_symbol_iterator
        : public iterator_facade<specific_symbol_iterator<SpecificType>> {
    public:
        /// Constructs a default iterator that points nowhere.
        specific_symbol_iterator() : current(nullptr) {}

        /// Constructs an iterator pointing at the given child symbol in the scope.
        ///
        /// @note If the given symbol is not of the desired type the iterator
        /// will be advanced until one is found or the end of the scope is reached.
        specific_symbol_iterator(const Symbol* firstSymbol) : current(firstSymbol) { skipToNext(); }

        /// Dereferences the iterator, resolving it to a symbol.
        const SpecificType& dereference() const { return current->as<SpecificType>(); }

        /// Advances the iterator to the next symbol in the scope
        /// that is of the desired type.
        void increment() {
            current = current->nextInScope;
            skipToNext();
        }

        /// @returns true if the given iterator is equal to this one.
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

    /// @brief Gets a pointer to the first member in the scope.
    ///
    /// @note This does not force elaboration of the scope.
    const Symbol* getFirstMember() const { return firstMember; }

    /// @brief Gets a pointer to the last member in the scope.
    ///
    /// @note This does not force elaboration of the scope.
    const Symbol* getLastMember() const { return lastMember; }

    /// Gets the map of names for child symbols in this scope.
    const SymbolMap& getNameMap() const {
        ensureElaborated();
        return *nameMap;
    }

    /// Gets the map of names for child symbols in this scope without
    /// forcing elaboration of the scope.
    const SymbolMap& getUnelaboratedNameMap() const { return *nameMap; }

    /// Reports a name conflict between the two given symbols in this scope.
    void reportNameConflict(const Symbol& member, const Symbol& existing) const;

    /// Collection of information about wildcard imports in a scope.
    class WildcardImportData {
    public:
        /// A list of wildcard import directives in the scope.
        std::vector<const WildcardImportSymbol*> wildcardImports;

        /// A name map of symbols that have imported thus far.
        /// This is mutated as the scope is elaborated.
        SymbolMap importedSymbols;

        /// True if we have called forceElaborate on this scope to
        /// ensure that we've seen all imported names.
        bool hasForceElaborated = false;
    };

    /// Gets the wildcard import data declared in this scope.
    WildcardImportData* getWildcardImportData() const { return importData; }

protected:
    Scope(Compilation& compilation_, const Symbol* thisSym_);

    /// Before we access any members to do lookups or return iterators, make sure
    /// the scope is fully elaborated.
    void ensureElaborated() const {
        if (needsElaboration)
            elaborate();
    }

    /// Flag the need for this scope to be elaborated before members are accessed.
    void setNeedElaboration() { needsElaboration = true; }

    /// Add a preconstructed wildcard import to this scope.
    void addWildcardImport(const WildcardImportSymbol& item);

    void insertMember(const Symbol* member, const Symbol* at, bool isElaborating,
                      bool incrementIndex) const;

private:
    friend class Compilation;

    void addDeferredMembers(const syntax::SyntaxNode& syntax);
    void elaborate() const;
    void handleNameConflict(const Symbol& member) const;
    void handleNameConflict(const Symbol& member, const Symbol*& existing,
                            bool isElaborating) const;
    void handleDataDeclaration(
        const ASTContext& context, const syntax::DataDeclarationSyntax& syntax,
        const Symbol*& insertionPoint,
        SmallVector<std::pair<const syntax::SyntaxNode*, const Symbol*>>& nonAnsiPortDecls) const;
    void handleNestedDefinition(const syntax::ModuleDeclarationSyntax& syntax) const;
    void handleExportedMethods() const;
    void checkImportConflict(const Symbol& member, const Symbol& existing) const;
    void addWildcardImport(const syntax::PackageImportItemSyntax& item,
                           std::span<const syntax::AttributeInstanceSyntax* const> attributes);

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

    // If this scope has any wildcard import directives we'll keep track of them
    // in a sideband object.
    WildcardImportData* importData = nullptr;

    // Set to true if the scope needs a separate elaboration pass before
    // its members can be accessed.
    mutable bool needsElaboration = false;

    // Indicates whether elaboration needs to do a prepass to add things like
    // enum values, deferred data declarations, etc.
    bool needsPrepass = false;

    // Indicates whether this scope is uncacheable, for instance if
    // it contains an extern iface method implementation.
    bool isUncacheable = false;

    // Indicates whether this scope has any exported modport subroutines.
    bool hasModportExports = false;
};

} // namespace slang::ast
