//------------------------------------------------------------------------------
//! @file Lookup.h
//! @brief Symbol lookup logic
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/diagnostics/Diagnostics.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/text/SourceLocation.h"
#include "slang/util/Util.h"

namespace slang::ast {

class ASTContext;
class ClassType;
class Scope;
class Symbol;
class SystemSubroutine;
class TempVarSymbol;
class Type;

enum class SymbolIndex : uint32_t;
enum class Visibility;

/// Additional modifiers for a lookup operation.
enum class SLANG_EXPORT LookupFlags {
    /// No special modifiers.
    None = 0,

    /// A lookup for a type name, as opposed to a value. These names cannot be hierarchical
    /// but can be package or class scoped.
    Type = 1 << 0,

    /// Usually lookups require that the found symbol be declared before the lookup
    /// location. This flag removes that restriction.
    AllowDeclaredAfter = 1 << 1,

    /// Don't search through wildcard imports to satisfy the lookup.
    DisallowWildcardImport = 1 << 2,

    /// Don't report an error if the lookup is for a simple identifier that
    /// cannot be found.
    NoUndeclaredError = 1 << 3,

    /// Don't report an error if the lookup is for a simple identifier that
    /// cannot be found *and* the context in which we are searching is an
    /// uninstantiated module.
    NoUndeclaredErrorIfUninstantiated = 1 << 4,

    /// The lookup is for a typedef target type, which has a special exemption
    /// to allow scoped access to incomplete forward class types.
    TypedefTarget = 1 << 5,

    /// The lookup should not continue looking into parent scopes if the name
    /// is not found in the initial search scope.
    NoParentScope = 1 << 6,

    /// Additional name selectors are not allowed in the final result.
    NoSelectors = 1 << 7,

    /// Lookup is allowed to return the root symbol via the '$root' scope specifier.
    AllowRoot = 1 << 8,

    /// Treat this lookup as hierarchical even if it's a simple name.
    ForceHierarchical = AllowDeclaredAfter | NoUndeclaredErrorIfUninstantiated
};
SLANG_BITMASK(LookupFlags, AllowRoot)

/// This type denotes the ordering of symbols within a particular scope, for the purposes of
/// determining whether a found symbol is visible compared to the given location.
/// For example, variables cannot be referenced before they are declared.
class SLANG_EXPORT LookupLocation {
public:
    LookupLocation() = default;
    LookupLocation(const Scope* scope_, uint32_t index) : scope(scope_), index(index) {}

    /// Gets the scope of the lookup. Note that this can be null.
    const Scope* getScope() const { return scope; }

    /// Gets the index within the scope for the lookup. This can be a sentinel value
    /// for the special `max` and `min` lookup locations.
    SymbolIndex getIndex() const { return SymbolIndex(index); }

    /// Places a location just before the given symbol in its parent scope.
    static LookupLocation before(const Symbol& symbol);

    /// Places a location just after the given symbol in its parent scope.
    static LookupLocation after(const Symbol& symbol);

    /// A special location that should always compare after any other.
    static const LookupLocation max;

    /// A special location that should always compare before any other.
    static const LookupLocation min;

    bool operator==(const LookupLocation& other) const = default;

    std::strong_ordering operator<=>(const LookupLocation& other) const {
        SLANG_ASSERT(scope == other.scope || !scope || !other.scope);
        return index <=> other.index;
    }

private:
    const Scope* scope = nullptr;
    uint32_t index = 0;
};

/// A structure that contains the results of a name lookup operation.
struct SLANG_EXPORT LookupResult {
    /// The symbol that was found by the lookup, or nullptr if no symbol was found.
    /// Note that there can still be errors even if a symbol is found.
    const Symbol* found = nullptr;

    /// If the lookup found a system subroutine, a pointer to it is returned here
    /// and the @a found field will be nullptr.
    const SystemSubroutine* systemSubroutine = nullptr;

    /// Set to true if the found symbol was imported from a package.
    bool wasImported = false;

    /// Set to true if the lookup was hierarchical.
    bool isHierarchical = false;

    /// Set to true if there were problems during lookup that indicate we should
    /// ignore the lack of a found symbol, because we're in a context where such
    /// a failure may be expected (for example, within a default instantiation of
    /// a generic class where the base class fails to resolve).
    bool suppressUndeclared = false;

    /// Set to true if the lookup was resolved through a type parameter. Some language
    /// rules restrict where this can be done.
    bool fromTypeParam = false;

    /// Set to true if the lookup was resolved through a forwarded typedef. Some language
    /// rules restrict where this can be done.
    bool fromForwardTypedef = false;

    /// A structure that represents a selection of a single member from the resulting
    /// symbol found during a lookup operation.
    struct MemberSelector {
        /// The name of the member to select.
        std::string_view name;

        /// The source location of the dot operator in the name path that
        /// led to selecting this member.
        SourceLocation dotLocation;

        /// The source range of the selection, for reporting diagnostics.
        SourceRange nameRange;
    };

    /// A type that represents a kind of selector for picking a child member
    /// from a found symbol. This can either be a dotted member select or
    /// an indexed element select (from an array).
    using Selector = std::variant<const syntax::ElementSelectSyntax*, MemberSelector>;

    /// A list of selectors that should be applied to the found symbol.
    /// Only applicable if the found symbol is a value symbol.
    SmallVector<Selector, 4> selectors;

    /// Reports a diagnostic that occurred during lookup. The stored diagnostics
    /// are not automatically emitted to the compilation, letting them be suppressed
    /// if desired.
    Diagnostic& addDiag(const Scope& scope, DiagCode code, SourceLocation location);

    /// Reports a diagnostic that occurred during lookup. The stored diagnostics
    /// are not automatically emitted to the compilation, letting them be suppressed
    /// if desired.
    Diagnostic& addDiag(const Scope& scope, DiagCode code, SourceRange sourceRange);

    /// Gets the list of diagnostics that occurred during lookup. The stored diagnostics
    /// are not automatically emitted to the compilation, letting them be suppressed
    /// if desired.
    const Diagnostics& getDiagnostics() const { return diagnostics; }

    /// Returns true if an error occurred during lookup.
    bool hasError() const;

    /// Clears the structure of all results, as if it had been default initialized.
    void clear();

    /// Copies result members from the given result object.
    void copyFrom(const LookupResult& other);

    /// Reports any diagnostics that have occurred during lookup to the given AST
    /// context, which will ensure they are visible to the compilation.
    void reportDiags(const ASTContext& context) const;

    /// Issues a diagnostic if there are selectors in the lookup result.
    void errorIfSelectors(const ASTContext& context) const;

private:
    Diagnostics diagnostics;
};

/// Centralized functionality for looking up symbols by name in the AST.
class SLANG_EXPORT Lookup {
public:
    /// Performs a full fledged name lookup starting in the current scope, following all
    /// SystemVerilog rules for qualified or unqualified name resolution.
    static void name(const syntax::NameSyntax& syntax, const ASTContext& context,
                     bitmask<LookupFlags> flags, LookupResult& result);

    /// Performs an unqualified lookup in this scope, then recursively up the parent
    /// chain until we reach root or the symbol is found. No errors are reported if
    /// no symbol can be found.
    static const Symbol* unqualified(const Scope& scope, std::string_view name,
                                     bitmask<LookupFlags> flags = LookupFlags::None);

    /// Performs an unqualified lookup in this scope, then recursively up the parent
    /// chain until we reach root or the symbol is found. Reports an error if
    /// the symbol is not found.
    static const Symbol* unqualifiedAt(const Scope& scope, std::string_view name,
                                       LookupLocation location, SourceRange sourceRange,
                                       bitmask<LookupFlags> flags = LookupFlags::None);

    /// Applies the given @a selectors to the @a symbol and returns the selected child.
    /// If any errors occur, diagnostics are issued to @a result and nullptr is returned.
    static const Symbol* selectChild(const Symbol& symbol,
                                     std::span<const syntax::ElementSelectSyntax* const> selectors,
                                     const ASTContext& context, LookupResult& result);

    /// Applies the given @a selectors to the @a virtualInterface type and returns the
    /// selected child in @result -- if any errors occur, diagnostics are issued to
    /// the result object and nullptr is returned.
    static void selectChild(const Type& virtualInterface, SourceRange range,
                            std::span<LookupResult::Selector> selectors, const ASTContext& context,
                            LookupResult& result);

    /// Searches for a class with the given @a name within @a context -- if no symbol is
    /// found, or if the found symbol is not a class type, appropriate diagnostics are issued.
    /// If @a requireInterfaceClass is given the resulting class will be required to be
    /// an interface class; nullptr will be returned and a diagnostic issued if it's not.
    static const ClassType* findClass(const syntax::NameSyntax& name, const ASTContext& context,
                                      std::optional<DiagCode> requireInterfaceClass = {});

    /// Gets the containing class for the given scope. The return value is a pair, with
    /// the first element being the found class or nullptr if the scope is not within a
    /// class definition. The second element indicates whether the given scope was found
    /// to be within a static method.
    static std::pair<const ClassType*, bool> getContainingClass(const Scope& scope);

    /// If the given symbol is a member of a class, returns its access visibility.
    /// Otherwise, returns Visibility::Public.
    static Visibility getVisibility(const Symbol& symbol);

    /// Returns whether the given @a symbol is visible from the provided scope,
    /// taking into account class accessibility modifiers.
    static bool isVisibleFrom(const Symbol& symbol, const Scope& scope);

    /// Returns whether the given @a target instance symbol is accessible from the
    /// provided scope, taking into account the class that owns the target (if any)
    /// and the class that owns the provided scope (if any). This is for checking
    /// access of instance members and doesn't look at visibility of the symbol.
    static bool isAccessibleFrom(const Symbol& target, const Symbol& sourceScope);

    /// If the given symbol is not a class member, returns true without doing any other work.
    /// Otherwise, if the member is visible from the provided context, returns true.
    /// If it's not visible, and @a sourceRange is provided, an appropriate diganostic will
    /// be issued and false returned.
    static bool ensureVisible(const Symbol& symbol, const ASTContext& context,
                              std::optional<SourceRange> sourceRange);

    /// If the given symbol is not a class member, returns true without doing any other work.
    /// Otherwise, if the member is accessible from the provided context (in terms of static
    /// vs instance members), returns true. If it's not accessible, and @a sourceRange is provided,
    /// an appropriate diganostic will be issued and false returned.
    static bool ensureAccessible(const Symbol& symbol, const ASTContext& context,
                                 std::optional<SourceRange> sourceRange);

    /// Searches a linked list of temporary variable symbols to see if any match the given name.
    /// If one is found, populates @a result and returns true. Otherwise returns false.
    static bool findTempVar(const Scope& scope, const TempVarSymbol& symbol,
                            const syntax::NameSyntax& name, LookupResult& result);

    /// Performs a lookup within the given class randomize() scope, respecting the name
    /// restrictions provided. If the symbol is not found, or if the name starts with 'local::',
    /// it is expected that the caller will then perform a normal lookup in the local scope.
    /// Returns true if the symbol is found and false otherwise.
    static bool withinClassRandomize(const ASTContext& context, const syntax::NameSyntax& syntax,
                                     bitmask<LookupFlags> flags, LookupResult& result);

    /// Performs a lookup within an expanding sequence or property to try to find a
    /// local variable matching the given name. If one is found, populates @a result
    /// and returns true. Otherwise returns false.
    static bool findAssertionLocalVar(const ASTContext& context, const syntax::NameSyntax& name,
                                      LookupResult& result);

private:
    Lookup() = default;

    static void unqualifiedImpl(const Scope& scope, std::string_view name, LookupLocation location,
                                std::optional<SourceRange> sourceRange, bitmask<LookupFlags> flags,
                                SymbolIndex outOfBlockIndex, LookupResult& result,
                                const Scope& originalScope);

    static void qualified(const syntax::ScopedNameSyntax& syntax, const ASTContext& context,
                          bitmask<LookupFlags> flags, LookupResult& result);

    static void reportUndeclared(const Scope& scope, std::string_view name, SourceRange range,
                                 bitmask<LookupFlags> flags, bool isHierarchical,
                                 LookupResult& result);
};

} // namespace slang::ast
