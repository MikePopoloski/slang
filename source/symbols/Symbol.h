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
#include "util/HashMap.h"
#include "util/Iterator.h"
#include "util/PointerUnion.h"

namespace slang {

class Statement;
class StatementList;
class Expression;
class SyntaxTree;
class Symbol;
class Scope;
class RootSymbol;
class Type;
class WildcardImportSymbol;
class PackageSymbol;
class ParameterSymbol;
class Compilation;
class StatementBodiedScope;

using SymbolList = span<const Symbol* const>;
using SymbolMap = flat_hash_map<string_view, const Symbol*>;
using Dimensions = span<ConstantRange const>;

/// Represents a definition (module, interface, or program) that can be instantiated
/// to form a node in the design hierarchy.
class Definition {
public:
    /// The syntax that defines the body of the definition.
    const ModuleDeclarationSyntax& syntax;

    /// The name of the definition.
    string_view name;

    /// Tracks info about each parameter declaration for later evaluation.
    struct ParameterDecl {
        /// The name of the parameter.
        string_view name;

        /// The syntax describing the parameter's data type. This is evaluated lazily
        /// into a real type since it may require doing inference from the value.
        const DataTypeSyntax* type = nullptr;

        /// The default initializer, or null if the parameter has no default.
        const ExpressionSyntax* initializer = nullptr;

        /// The source location of the parameter.
        SourceLocation location;

        /// Indicates whether the parameter is a localparam (not overridable).
        bool isLocal;

        /// Indicates whether the parameter was declared in the header (parameter port list) or
        /// within the body of the definition itself.
        bool isPort;
    };

    /// A list of parameter declarations within the definition.
    span<const ParameterDecl> parameters;

    explicit Definition(const ModuleDeclarationSyntax& syntax) :
        syntax(syntax), name(syntax.header.name.valueText()) {}
};

enum class SymbolKind {
    Unknown,
    Root,
    CompilationUnit,
    TransparentMember,
    BuiltInIntegerType,
    VectorType,
    FloatingType,
    EnumType,
    EnumValue,
    PackedArrayType,
    UnpackedArrayType,
    PackedStructType,
    UnpackedStructType,
    PackedUnionType,
    UnpackedUnionType,
    
    ClassType,
    VoidType,
    NullType,
    CHandleType,
    StringType,
    EventType,
    TypeAlias,
    ErrorType,
    Parameter,
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

        const TSource* getSourceOrNull() const {
            if (cache.index() == 0)
                return nullptr;
            return std::get<1>(cache);
        }

        bool hasResult() const { return cache.index() == 0 && std::get<0>(cache); }

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

    LAZY(LazyInitializer, Expression, ExpressionSyntax);
    LAZY(LazyType, Type, DataTypeSyntax);

#undef LAZY

protected:
    explicit Symbol(SymbolKind kind, string_view name, SourceLocation location) :
        kind(kind), name(name), location(location) {}

    Symbol(const Symbol&) = delete;

    Diagnostic& addError(DiagCode code, SourceLocation location) const;

    void setParent(const Scope& scope) { parentScope = &scope; }

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

        void registerTransparentType(const Symbol* symbol, const Symbol::LazyType& type) {
            transparentTypes.emplace(symbol, &type);
        }

        using TransparentTypeMap = flat_hash_map<const Symbol*, const Symbol::LazyType*>;
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

        iterator& operator++() {
            current = current->nextInScope;
            return *this;
        }

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

/// Base class for scopes that have a statement body.
class StatementBodiedScope : public Scope {
public:
    const Statement* getBody() const {
        ensureMembers();
        return body;
    }

    void setBody(const Statement* statement) { body = statement; }
    void setBody(const StatementSyntax& syntax);
    void setBody(const SyntaxList<SyntaxNode>& syntax);

protected:
    using Scope::Scope;

private:
    friend class Scope;

    void bindBody(const SyntaxNode& syntax);
    void bindVariableDecl(const DataDeclarationSyntax& syntax, SmallVector<const Statement*>& statements);

    Statement& bindStatement(const StatementSyntax& syntax);
    Statement& bindStatementList(const SyntaxList<SyntaxNode>& items);
    Statement& bindReturnStatement(const ReturnStatementSyntax& syntax);
    Statement& bindConditionalStatement(const ConditionalStatementSyntax& syntax);
    Statement& bindForLoopStatement(const ForLoopStatementSyntax& syntax);
    Statement& bindExpressionStatement(const ExpressionStatementSyntax& syntax);

    Statement& badStmt(const Statement* stmt);

    const Statement* body = nullptr;
};

/// A class that wraps a hoisted transparent type member (such as an enum value)
/// into a parent scope. Whenever lookup finds one of these symbols, it will be
/// unwrapped into the underlying symbol instead.
class TransparentMemberSymbol : public Symbol {
public:
    const Symbol& wrapped;

    TransparentMemberSymbol(const Symbol& wrapped_) :
        Symbol(SymbolKind::TransparentMember, wrapped_.name, wrapped_.location),
        wrapped(wrapped_) {}
};

/// The root of a single compilation unit.
class CompilationUnitSymbol : public Symbol, public Scope {
public:
    explicit CompilationUnitSymbol(Compilation& compilation) :
        Symbol(SymbolKind::CompilationUnit, "", SourceLocation()),
        Scope(compilation, this) {}
};

/// A SystemVerilog package construct.
class PackageSymbol : public Symbol, public Scope {
public:
    PackageSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(SymbolKind::Package, name, loc),
        Scope(compilation, this) {}

    static PackageSymbol& fromSyntax(Compilation& compilation, const ModuleDeclarationSyntax& syntax);
};

/// Base class for module, interface, and program instance symbols.
class InstanceSymbol : public Symbol, public Scope {
public:
    static void fromSyntax(Compilation& compilation, const HierarchyInstantiationSyntax& syntax,
                           const Scope& scope, SmallVector<const Symbol*>& results);

protected:
    InstanceSymbol(SymbolKind kind, Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(kind, name, loc),
        Scope(compilation, this) {}
};

class ModuleInstanceSymbol : public InstanceSymbol {
public:
    ModuleInstanceSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        InstanceSymbol(SymbolKind::ModuleInstance, compilation, name, loc) {}

    static ModuleInstanceSymbol& instantiate(Compilation& compilation, string_view name, SourceLocation loc,
                                             const Definition& definition);

    struct ParameterMetadata {
        const Definition::ParameterDecl* decl;
        const Type* type;
        ConstantValue value;
    };

    static ModuleInstanceSymbol& instantiate(Compilation& compilation, string_view name, SourceLocation loc,
                                             const Definition& definition, span<const ParameterMetadata> parameters);
};

class SequentialBlockSymbol : public Symbol, public StatementBodiedScope {
public:
    SequentialBlockSymbol(Compilation& compilation, SourceLocation loc) :
        Symbol(SymbolKind::SequentialBlock, "", loc),
        StatementBodiedScope(compilation, this) {}
};

class ProceduralBlockSymbol : public Symbol, public StatementBodiedScope {
public:
    ProceduralBlockKind procedureKind;

    ProceduralBlockSymbol(Compilation& compilation, SourceLocation loc, ProceduralBlockKind procedureKind) :
        Symbol(SymbolKind::ProceduralBlock, "", loc),
        StatementBodiedScope(compilation, this),
        procedureKind(procedureKind) {}
};

/// Represents blocks that are instantiated by a loop generate or conditional
/// generate construct. These blocks can contain a bunch of members, or just
/// a single item. They can also contain an implicit parameter representing
/// the loop iteration value.
class GenerateBlockSymbol : public Symbol, public Scope {
public:
    GenerateBlockSymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(SymbolKind::GenerateBlock, name, loc),
        Scope(compilation, this) {}

    /// Creates a generate block from the given if-generate syntax node. Note that
    /// this can return null if the condition is false and there is no else block.
    static GenerateBlockSymbol* fromSyntax(Compilation& compilation, const IfGenerateSyntax& syntax,
                                           const Scope& parent);
};

/// Represents an array of generate blocks, as generated by a loop generate construct.
class GenerateBlockArraySymbol : public Symbol, public Scope {
public:
    GenerateBlockArraySymbol(Compilation& compilation, string_view name, SourceLocation loc) :
        Symbol(SymbolKind::GenerateBlockArray, name, loc),
        Scope(compilation, this) {}

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

/// Represents a parameter value.
class ParameterSymbol : public Symbol {
public:
    ParameterSymbol(string_view name, SourceLocation loc, bool isLocal_, bool isPort_) :
        Symbol(SymbolKind::Parameter, name, loc),
        type(this), isLocal(isLocal_), isPort(isPort_) {}

    static void fromSyntax(Compilation& compilation, const ParameterDeclarationSyntax& syntax,
                           SmallVector<ParameterSymbol*>& results);

    static ParameterSymbol& fromDecl(Compilation& compilation, const Definition::ParameterDecl& decl);

    static std::tuple<const Type*, ConstantValue> evaluate(const DataTypeSyntax& type,
                                                           const ExpressionSyntax& expr, const Scope& scope);

    void setDeclaredType(const DataTypeSyntax& syntax) { declaredType = &syntax; type = syntax; }
    const DataTypeSyntax* getDeclaredType() const { return declaredType; }

    const Type& getType() const;
    void setType(const Type& newType) { type = newType; }

    const LazyType& getLazyType() const { return type; }

    const ConstantValue& getValue() const;
    void setValue(ConstantValue value);

    const ConstantValue* getDefault() const;
    void setDefault(ConstantValue&& value);
    void setDefault(const ExpressionSyntax& syntax);

    bool hasDefault() const { return (bool)defaultValue; }
    bool isLocalParam() const { return isLocal; }
    bool isPortParam() const { return isPort; }
    bool isBodyParam() const { return !isPortParam(); }

private:
    const DataTypeSyntax* declaredType = nullptr;
    mutable LazyType type;
    mutable const ConstantValue* value = nullptr;
    mutable PointerUnion<const ConstantValue*, const ExpressionSyntax*> defaultValue;
    bool isLocal = false;
    bool isPort = false;
};

/// Represents a variable declaration (which does not include nets).
class VariableSymbol : public Symbol {
public:
    LazyType type;
    LazyInitializer initializer;
    VariableLifetime lifetime;
    bool isConst;

    VariableSymbol(string_view name, SourceLocation loc,
                   VariableLifetime lifetime = VariableLifetime::Automatic, bool isConst = false) :
        VariableSymbol(SymbolKind::Variable, name, loc, lifetime, isConst) {}

    /// Constructs all variable symbols specified by the given syntax node.
    static void fromSyntax(Compilation& compilation, const DataDeclarationSyntax& syntax,
                           SmallVector<const VariableSymbol*>& results);

    static VariableSymbol& fromSyntax(Compilation& compilation, const ForVariableDeclarationSyntax& syntax);

protected:
    VariableSymbol(SymbolKind childKind, string_view name, SourceLocation loc,
                   VariableLifetime lifetime = VariableLifetime::Automatic, bool isConst = false) :
        Symbol(childKind, name, loc),
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
        VariableSymbol(SymbolKind::FormalArgument, "", SourceLocation()) {}

    FormalArgumentSymbol(string_view name, SourceLocation loc,
                         FormalArgumentDirection direction = FormalArgumentDirection::In) :
        VariableSymbol(SymbolKind::FormalArgument, name, loc, VariableLifetime::Automatic,
                       direction == FormalArgumentDirection::ConstRef),
        direction(direction) {}
};

/// Represents a subroutine (task or function).
class SubroutineSymbol : public Symbol, public StatementBodiedScope {
public:
    using ArgList = span<const FormalArgumentSymbol* const>;

    LazyType returnType;
    ArgList arguments;
    VariableLifetime defaultLifetime = VariableLifetime::Automatic;
    SystemFunction systemFunctionKind = SystemFunction::Unknown;
    bool isTask = false;

    SubroutineSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                     VariableLifetime defaultLifetime, bool isTask) :
        Symbol(SymbolKind::Subroutine, name, loc),
        StatementBodiedScope(compilation, this),
        returnType(static_cast<const Scope*>(this)),
        defaultLifetime(defaultLifetime), isTask(isTask) {}

    SubroutineSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                     SystemFunction systemFunction) :
        Symbol(SymbolKind::Subroutine, name, loc),
        StatementBodiedScope(compilation, this),
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
        Symbol(SymbolKind::Root, "", SourceLocation()), Scope(compilation, this) {}
};

}
