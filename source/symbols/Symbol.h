//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <tuple>
#include <vector>

#include "flat_hash_map.hpp"

#include "binding/ConstantValue.h"
#include "diagnostics/Diagnostics.h"
#include "parsing/AllSyntax.h"
#include "symbols/SemanticFacts.h"
#include "text/SourceLocation.h"
#include "util/Iterator.h"
#include "util/PointerUnion.h"

namespace slang {

class DefinitionSymbol;
class Statement;
class StatementList;
class Expression;
class SyntaxTree;
class Symbol;
class Scope;
class RootSymbol;
class TypeSymbol;
class WildcardImportSymbol;
class PackageSymbol;
class ParameterSymbol;
class Compilation;

using SymbolList = span<const Symbol* const>;
using SymbolMap = flat_hash_map<string_view, const Symbol*>;
using ParamOverrideMap = flat_hash_map<const ParameterSymbol*, const ExpressionSyntax*>;
using Dimensions = span<ConstantRange const>;

enum class SymbolKind {
    Unknown,
    Root,
    CompilationUnit,
    IntegralType,
    RealType,
    StringType,
    CHandleType,
    VoidType,
    EventType,
    EnumType,
    TypeAlias,
    Parameter,
    EnumValue,
    Module,
    Interface,
    Modport,
    ModuleInstance,
    InterfaceInstance,
    Package,
    ExplicitImport,
    WildcardImport,
    Program,
    Attribute,
    Genvar,
    GenerateBlock,
    GenerateBlockArray,
    ProceduralBlock,
    SequentialBlock,
    Variable,
    Instance,
    FormalArgument,
    Subroutine
};

/// Base class for all symbols (logical code constructs) such as modules, types,
/// functions, variables, etc.
class Symbol {
public:
    /// The type of symbol.
    SymbolKind kind;

    /// The name of the symbol; if the symbol does not have a name,
    /// this will be an empty string.
    string_view name;

    /// The declared location of the symbol in the source code, or an empty location
    /// if it was not explicitly declared in the source text. This is mainly used
    /// for reporting errors.
    SourceLocation location;

    /// Gets the lexical scope that contains this symbol.
    const Scope* getScope() const { return parentScope; }

    /// Finds the first ancestor symbol of the given kind. If this symbol is already of
    /// the given kind, returns this symbol.
    const Symbol* findAncestor(SymbolKind searchKind) const;

    template<typename T>
    T& as() { return *static_cast<T*>(this); }

    template<typename T>
    const T& as() const { return *static_cast<const T*>(this); }

    /// Makes a clone of the symbol. The cloned symbol has the same properties as
    /// the original but will not be a member of any scope.
    Symbol& clone() const;

    /// A numeric index that can be used to compare the relative ordering of symbols
    /// within a single lexical scope.
    enum class Index : uint32_t {};

    /// Gets the index of the symbol within its parent scope, which can be used
    /// to determine the relative ordering of scope members.
    Index getIndex() const { return indexInScope; }

    template<typename TDerived, typename TResult, typename TSource>
    struct Lazy {
        using ScopeOrSymbol = PointerUnion<const Scope*, const Symbol*>;

        Lazy(ScopeOrSymbol parent, const TResult* init) : parent(parent), cache(init) {}
        Lazy(ScopeOrSymbol parent, const TSource& init) : parent(parent), cache(&init) {}

        Lazy& operator=(const TResult* result) { cache = result; return *this; }
        Lazy& operator=(const TResult& result) { cache = &result; return *this; }
        Lazy& operator=(const TSource& source) { cache = &source; return *this; }

        const TResult& operator*() const { return *get(); }

        const TResult* operator->() const { return get(); }

        explicit operator bool() const { return get(); }

        const TResult* get() const {
            if (cache.index() == 0)
                return std::get<0>(cache);

            auto derived = static_cast<const TDerived*>(this);
            const TResult& result = derived->evaluate(getScope(), *std::get<1>(cache));
            cache = &result;
            return &result;
        }

    protected:
        const Scope& getScope() const {
            if (parent.is<const Symbol*>())
                return *parent.get<const Symbol*>()->getScope();
            else
                return *parent.get<const Scope*>();
        }

    private:
        ScopeOrSymbol parent;
        mutable std::variant<const TResult*, const TSource*> cache;
    };

    struct LazyConstant : public Lazy<LazyConstant, ConstantValue, ExpressionSyntax> {
        explicit LazyConstant(ScopeOrSymbol parent);
        LazyConstant(ScopeOrSymbol parent, const ConstantValue* init) :
            Lazy<LazyConstant, ConstantValue, ExpressionSyntax>(parent, init) {}
        LazyConstant(ScopeOrSymbol parent, const ExpressionSyntax& init) :
            Lazy<LazyConstant, ConstantValue, ExpressionSyntax>(parent, init) {}

        LazyConstant& operator=(const ExpressionSyntax& source);
        LazyConstant& operator=(ConstantValue result);

    private:
        friend struct Lazy<LazyConstant, ConstantValue, ExpressionSyntax>;
        const ConstantValue& evaluate(const Scope& scope, const ExpressionSyntax& source) const;
    };

#define LAZY(name, TResult, TSource)                            \
    struct name : public Lazy<name, TResult, TSource> {         \
        explicit name(ScopeOrSymbol parent);                    \
        name(ScopeOrSymbol parent, const TResult* init) :       \
            Lazy<name, TResult, TSource>(parent, init) {}       \
        name(ScopeOrSymbol parent, const TSource& init) :       \
            Lazy<name, TResult, TSource>(parent, init) {}       \
        using Lazy<name, TResult, TSource>::operator=;          \
    private:                                                    \
        friend struct Lazy<name, TResult, TSource>;             \
        const TResult& evaluate(const Scope& scope, const TSource& source) const; \
    }

    LAZY(LazyStatement, Statement, StatementSyntax);
    LAZY(LazyStatementList, StatementList, SyntaxList<SyntaxNode>);
    LAZY(LazyInitializer, Expression, ExpressionSyntax);
    LAZY(LazyType, TypeSymbol, DataTypeSyntax);

#undef LAZY

protected:
    explicit Symbol(SymbolKind kind, string_view name = "", SourceLocation location = SourceLocation()) :
        kind(kind), name(name), location(location) {}

    Diagnostic& addError(DiagCode code, SourceLocation location) const;

private:
    friend class Scope;

    // When a symbol is first added to a scope a pointer to it will be stored here.
    // Along with that pointer, a linked list of members in the scope will be created
    // by using the nextInScope pointer, and the index within the scope (used to quickly
    // determine ordering during lookups) will set here.
    mutable const Scope* parentScope = nullptr;
    mutable const Symbol* nextInScope = nullptr;
    mutable Index indexInScope {0};
};

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

    /// Name referenced is the target of a hierarchy instantiation. Local scopes will be
    /// searched for nested modules before looking in the root definitions namespace.
    Definition,

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

    const Scope* getParent() const { return thisSym->getScope(); }
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
    ConstantValue evaluateConstant(const ExpressionSyntax& expr) const;

    /// A helper method to evaluate a constant in the current scope and then
    /// convert it to the given destination type. If the conversion fails, the
    /// returned value will be marked bad.
    ConstantValue evaluateConstantAndConvert(const ExpressionSyntax& expr, const TypeSymbol& targetType,
                                             SourceLocation errorLocation) const;

    /// Strongly typed index type which is used in a sideband list in the Compilation object
    /// to store information about deferred members in this scope.
    enum class DeferredMemberIndex : uint32_t { Invalid = 0 };

    /// Data stored in sideband tables in the Compilation object for deferred members.
    /// If the scope has deferred members, it will store a list of syntax nodes that need
    /// to be elaborated, along with a pointer to the symbol in the scope that marks where
    /// the elaborated members should be inserted.
    using DeferredMemberData = std::vector<std::tuple<const SyntaxNode*, const Symbol*>>;

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

        iterator& operator++() {
            current = current->nextInScope;
            return *this;
        }

    private:
        const Symbol* current;
    };

    /// Gets the members contained in the scope.
    iterator_range<iterator> members() const {
        ensureMembers();
        return { iterator(firstMember), iterator(nullptr) };
    }

protected:
    Scope(Compilation& compilation_, const Symbol* thisSym_);

private:
    // Inserts the given member symbol into our own list of members, right after
    // the given symbol. If `at` is null, it will insert at the head of the list.
    void insertMember(const Symbol* member, const Symbol* at) const;

    // Adds a deferred member to the scope, which is tracked in the Compilation object
    // and will later be elaborated by `realizeDeferredMembers`.
    void addDeferredMember(const SyntaxNode& member);

    // Before we access any members to do lookups or return iterators, make sure
    // we don't have any deferred members to take care of first.
    void realizeDeferredMembers() const;
    void ensureMembers() const {
        if (deferredMemberIndex != DeferredMemberIndex::Invalid)
            realizeDeferredMembers();
    }

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

/// The root of a single compilation unit.
class CompilationUnitSymbol : public Symbol, public Scope {
public:
    explicit CompilationUnitSymbol(Compilation& compilation) :
        Symbol(SymbolKind::CompilationUnit), Scope(compilation, this) {}
};

/// A SystemVerilog package construct.
class PackageSymbol : public Symbol, public Scope {
public:
    PackageSymbol(Compilation& compilation, string_view name) :
        Symbol(SymbolKind::Package, name), Scope(compilation, this) {}

    static PackageSymbol& fromSyntax(Compilation& compilation, const ModuleDeclarationSyntax& syntax);
};

/// Represents a module, interface, or program declaration.
class DefinitionSymbol : public Symbol, public Scope {
public:
    span<const ParameterSymbol* const> parameters;

    DefinitionSymbol(Compilation& compilation, string_view name) :
        Symbol(SymbolKind::Module, name), Scope(compilation, this) {}

    static DefinitionSymbol& fromSyntax(Compilation& compilation, const ModuleDeclarationSyntax& syntax);

    void createParamOverrides(const ParameterValueAssignmentSyntax& syntax, ParamOverrideMap& map) const;
};

/// Base class for module, interface, and program instance symbols.
class InstanceSymbol : public Symbol, public Scope {
public:
    const DefinitionSymbol& definition;

    static void fromSyntax(Compilation& compilation, const HierarchyInstantiationSyntax& syntax,
                           const Scope& scope, SmallVector<const Symbol*>& results);

protected:
    InstanceSymbol(SymbolKind kind, Compilation& compilation, string_view name,
                   const DefinitionSymbol& definition) :
        Symbol(kind, name),
        Scope(compilation, this),
        definition(definition) {}
};

class ModuleInstanceSymbol : public InstanceSymbol {
public:
    ModuleInstanceSymbol(Compilation& compilation, string_view name, const DefinitionSymbol& definition) :
        InstanceSymbol(SymbolKind::ModuleInstance, compilation, name, definition) {}
};

class SequentialBlockSymbol : public Symbol, public Scope {
public:
    LazyStatement body;

    explicit SequentialBlockSymbol(Compilation& compilation) :
        Symbol(SymbolKind::SequentialBlock),
        Scope(compilation, this),
        body(static_cast<const Scope*>(this)) {}

    static SequentialBlockSymbol& createImplicitBlock(Compilation& compilation,
                                                      const ForLoopStatementSyntax& forLoop);
};

class ProceduralBlockSymbol : public Symbol, public Scope {
public:
    LazyStatement body;
    ProceduralBlockKind procedureKind;

    ProceduralBlockSymbol(Compilation& compilation, ProceduralBlockKind procedureKind) :
        Symbol(SymbolKind::ProceduralBlock),
        Scope(compilation, this),
        body(static_cast<const Scope*>(this)),
        procedureKind(procedureKind) {}
};

/// Represents blocks that are instantiated by a loop generate or conditional
/// generate construct. These blocks can contain a bunch of members, or just
/// a single item. They can also contain an implicit parameter representing
/// the loop iteration value.
class GenerateBlockSymbol : public Symbol, public Scope {
public:
    GenerateBlockSymbol(Compilation& compilation, string_view name) :
        Symbol(SymbolKind::GenerateBlock, name), Scope(compilation, this) {}

    /// Creates a generate block from the given if-generate syntax node. Note that
    /// this can return null if the condition is false and there is no else block.
    static GenerateBlockSymbol* fromSyntax(Compilation& compilation, const IfGenerateSyntax& syntax,
                                           const Scope& parent);
};

/// Represents an array of generate blocks, as generated by a loop generate construct.
class GenerateBlockArraySymbol : public Symbol, public Scope {
public:
    GenerateBlockArraySymbol(Compilation& compilation, string_view name) :
        Symbol(SymbolKind::GenerateBlockArray, name), Scope(compilation, this) {}

    /// Creates a generate block array from the given loop-generate syntax node.
    static GenerateBlockArraySymbol& fromSyntax(Compilation& compilation,
                                                const LoopGenerateSyntax& syntax, const Scope& parent);
};

/// Represents an explicit import from a package. This symbol type is
/// special in that it won't be returned from a lookup() call; instead
/// it will be unwrapped into the imported symbol.
class ExplicitImportSymbol : public Symbol {
public:
    string_view packageName;
    string_view importName;

    ExplicitImportSymbol(string_view packageName, string_view importName, SourceLocation location) :
        Symbol(SymbolKind::ExplicitImport, importName, location),
        packageName(packageName), importName(importName) {}

    const PackageSymbol* package() const;
    const Symbol* importedSymbol() const;

private:
    mutable const PackageSymbol* package_ = nullptr;
    mutable const Symbol* import = nullptr;
    mutable bool initialized = false;
};

/// Represents a wildcard import declaration. This symbol is special in
/// that it won't be returned by a lookup, and won't even be in the name
/// map of a symbol at all. Instead there is a sideband list used to
/// resolve names via wildcard.
class WildcardImportSymbol : public Symbol {
public:
    string_view packageName;

    WildcardImportSymbol(string_view packageName, SourceLocation location) :
        Symbol(SymbolKind::WildcardImport, "", location),
        packageName(packageName) {}

    const PackageSymbol* getPackage() const;

private:
    mutable optional<const PackageSymbol*> package;
};

class ParameterSymbol : public Symbol {
public:
    LazyConstant defaultValue;
    LazyConstant value;
    bool isLocalParam = false;
    bool isPortParam = false;

    ParameterSymbol(string_view name) :
        Symbol(SymbolKind::Parameter, name),
        defaultValue(this),
        value(this) {}

    static void fromSyntax(Compilation& compilation, const ParameterDeclarationSyntax& syntax,
                           SmallVector<ParameterSymbol*>& results);
};

/// Represents a variable declaration (which does not include nets).
class VariableSymbol : public Symbol {
public:
    LazyType type;
    LazyInitializer initializer;
    VariableLifetime lifetime;
    bool isConst;

    VariableSymbol(string_view name, VariableLifetime lifetime = VariableLifetime::Automatic,
                   bool isConst = false) :
        VariableSymbol(SymbolKind::Variable, name, lifetime, isConst) {}

    /// Constructs all variable symbols specified by the given syntax node.
    static void fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                           SmallVector<const VariableSymbol*>& results);

protected:
    VariableSymbol(SymbolKind childKind, string_view name,
                   VariableLifetime lifetime = VariableLifetime::Automatic, bool isConst = false) :
        Symbol(childKind, name),
        type(this),
        initializer(this),
        lifetime(lifetime),
        isConst(isConst) {}
};

/// Represents a formal argument in subroutine (task or function).
class FormalArgumentSymbol : public VariableSymbol {
public:
    FormalArgumentDirection direction = FormalArgumentDirection::In;

    FormalArgumentSymbol() :
        VariableSymbol(SymbolKind::FormalArgument, "") {}

    FormalArgumentSymbol(string_view name, FormalArgumentDirection direction = FormalArgumentDirection::In) :
        VariableSymbol(SymbolKind::FormalArgument, name, VariableLifetime::Automatic,
                       direction == FormalArgumentDirection::ConstRef),
        direction(direction) {}
};

/// Represents a subroutine (task or function).
class SubroutineSymbol : public Symbol, public Scope {
public:
    using ArgList = span<const FormalArgumentSymbol* const>;

    LazyStatementList body;
    LazyType returnType;
    ArgList arguments;
    VariableLifetime defaultLifetime = VariableLifetime::Automatic;
    SystemFunction systemFunctionKind = SystemFunction::Unknown;
    bool isTask = false;

    SubroutineSymbol(Compilation& compilation, string_view name, VariableLifetime defaultLifetime, bool isTask) :
        Symbol(SymbolKind::Subroutine, name),
        Scope(compilation, this),
        body(static_cast<const Scope*>(this)),
        returnType(static_cast<const Scope*>(this)),
        defaultLifetime(defaultLifetime), isTask(isTask) {}

    SubroutineSymbol(Compilation& compilation, string_view name, SystemFunction systemFunction) :
        Symbol(SymbolKind::Subroutine, name),
        Scope(compilation, this),
        body(static_cast<const Scope*>(this)),
        returnType(static_cast<const Scope*>(this)),
        systemFunctionKind(systemFunction) {}

    static SubroutineSymbol& fromSyntax(Compilation& compilation, const FunctionDeclarationSyntax& syntax);

    bool isSystemFunction() const { return systemFunctionKind != SystemFunction::Unknown; }
};

/// Represents the entirety of a design, along with all contained compilation units.
class RootSymbol : public Symbol, public Scope {
public:
    span<const ModuleInstanceSymbol* const> topInstances;
    span<const CompilationUnitSymbol* const> compilationUnits;

    explicit RootSymbol(Compilation& compilation) :
        Symbol(SymbolKind::Root), Scope(compilation, this) {}
};

}
