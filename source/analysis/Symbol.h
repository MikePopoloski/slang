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

#include "diagnostics/Diagnostics.h"
#include "parsing/AllSyntax.h"
#include "text/SourceLocation.h"
#include "util/Iterator.h"

#include "ConstantValue.h"
#include "SemanticFacts.h"
#include "SymbolMap.h"

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
class SymbolFactory;
class SymbolMap;

using SymbolList = span<const Symbol* const>;
using ParamOverrideMap = flat_hash_map<const ParameterSymbol*, const ExpressionSyntax*>;
using Dimensions = span<ConstantRange const>;

enum class SymbolKind {
    Unknown,
    Root,
    DynamicScope,
    CompilationUnit,
    LazySyntax,
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

    /// Gets the symbol for the root of the design.
    const RootSymbol& getRoot() const;

    template<typename T>
    T& as() { return *static_cast<T*>(this); }

    template<typename T>
    const T& as() const { return *static_cast<const T*>(this); }

    /// Makes a clone of the symbol with the provided scope as the new parent.
    Symbol& clone(const Scope& newParent) const;

    template<typename TDerived, typename TResult, typename TSource>
    struct Lazy {
        Lazy(const Scope* scope, const TResult* init) : storedScope(scope), cache(init) {}
        Lazy(const Scope* scope, const TSource& init) : storedScope(scope), cache(&init) {}

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
            const TResult& result = derived->evaluate(*storedScope, *std::get<1>(cache));
            cache = &result;
            return &result;
        }

    protected:
        const Scope* storedScope;

    private:
        mutable std::variant<const TResult*, const TSource*> cache;
    };

    struct LazyConstant : public Lazy<LazyConstant, ConstantValue, ExpressionSyntax> {
        explicit LazyConstant(const Scope* scope);
        LazyConstant(const Scope* scope, const ConstantValue* init) :
            Lazy<LazyConstant, ConstantValue, ExpressionSyntax>(scope, init) {}
        LazyConstant(const Scope* scope, const ExpressionSyntax& init) :
            Lazy<LazyConstant, ConstantValue, ExpressionSyntax>(scope, init) {}

        LazyConstant& operator=(const ExpressionSyntax& source);
        LazyConstant& operator=(ConstantValue result);

    private:
        friend struct Lazy<LazyConstant, ConstantValue, ExpressionSyntax>;
        const ConstantValue& evaluate(const Scope& scope, const ExpressionSyntax& source) const;
    };

#define LAZY(name, TResult, TSource)                            \
    struct name : public Lazy<name, TResult, TSource> {         \
        explicit name(const Scope* scope);                \
        name(const Scope* scope, const TResult* init) :   \
            Lazy<name, TResult, TSource>(scope, init) {}        \
        name(const Scope* scope, const TSource& init) :   \
            Lazy<name, TResult, TSource>(scope, init) {}        \
        using Lazy<name, TResult, TSource>::operator=;          \
    private:                                                    \
        friend struct Lazy<name, TResult, TSource>;             \
        const TResult& evaluate(const Scope& scope, const TSource& source) const; \
    }

    LAZY(LazyStatement, Statement, StatementSyntax);
    LAZY(LazyStatementList, StatementList, SyntaxList<SyntaxNode>);
    LAZY(LazyInitializer, Expression, ExpressionSyntax);
    LAZY(LazyType, TypeSymbol, DataTypeSyntax);

    // TODO: move this stuff to its own header / namespace
    struct LazyDefinition {
        using Source = const HierarchyInstantiationSyntax*;
        using Value = std::tuple<const DefinitionSymbol*, ParamOverrideMap>;

        LazyDefinition(const Scope* scope, Source source) : scope(scope), cache(source) {}
        const Value& get() const;

    private:
        const Scope* scope;
        mutable std::variant<Value, Source> cache;
    };

#undef LAZY

protected:
    explicit Symbol(SymbolKind kind, string_view name = "", SourceLocation location = SourceLocation()) :
        kind(kind), name(name), location(location) {}

    Symbol(SymbolKind kind, const Scope& containingSymbol, string_view name = "",
           SourceLocation location = SourceLocation()) :
        kind(kind), name(name), location(location),
        parentScope(&containingSymbol) {}

    Symbol(SymbolKind kind, Token token, const Scope& containingSymbol) :
        kind(kind), name(token.valueText()), location(token.location()),
        parentScope(&containingSymbol) {}

    Diagnostic& addError(DiagCode code, SourceLocation location) const;

private:
    const Scope* parentScope = nullptr;
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
    static const LookupRefPoint any;

    bool operator==(const LookupRefPoint& other) const {
        return scope == other.scope && index == other.index;
    }

    bool operator!=(const LookupRefPoint& other) const { return !(*this == other); }
    bool operator<(const LookupRefPoint& other) const;

private:
    friend class Scope;

    LookupRefPoint(const Scope& scope, uint32_t index) :
        scope(&scope), index(index) {}

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

    /// Sets the found symbol that is the result of successful lookup.
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
    const Scope* getParent() const { return thisSym->getScope(); }
    const Symbol& asSymbol() const { return *thisSym; }
    SymbolFactory& getFactory() const;

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

    /// Gets a list of all of the members in the scope.
    SymbolList members() const {
        if (!nameMap)
            buildNameMap();
        return memberList;
    }

    /// Sets the list of members in the scope. A copy of the provided span will be
    /// made so the provided memory need not outlive the call.
    void setMembers(SymbolList members);

    /// Gets a specific member at the given zero-based index, expecting it to be of the specified type.
    /// If the type does not match, this will assert.
    template<typename T>
    const T& member(uint32_t index) const { return members()[index]->as<T>(); }

    /// A helper method to evaluate a constant in the current scope.
    ConstantValue evaluateConstant(const ExpressionSyntax& expr) const;

    /// A helper method to evaluate a constant in the current scope and then
    /// convert it to the given destination type. If the conversion fails, the
    /// returned value will be marked bad.
    ConstantValue evaluateConstantAndConvert(const ExpressionSyntax& expr, const TypeSymbol& targetType,
                                             SourceLocation errorLocation) const;

protected:
    Scope(const Symbol* symbol) : thisSym(symbol) {}

private:
    const SymbolMap::NameEntry* lookupInternal(string_view name) const;
    void buildNameMap() const;

    // The list of members assigned to this scope.
    span<const Symbol*> memberList;

    // A list of wildcard imports that occur in this scope. Note that the entries in the
    // list are ordered by index, though they are probably not contiguous.
    struct ImportEntry {
        const WildcardImportSymbol* import;
        uint32_t index;
    };
    mutable span<ImportEntry> imports;

    // The map of names to members that can be looked up within this scope. This is built
    // on demand the first time a name lookup is performed. This map can contain names from
    // symbols that are lexically in other scopes but have been made visible here, such
    // as with enum values and package imports.
    mutable SymbolMap* nameMap = nullptr;

    // A pointer to symbol that this scope represents.
    const Symbol* thisSym;
};

/// A scope that can be dynamically modified programmatically. Not used for batch compilation; intended
/// for tools and unit tests.
class DynamicScopeSymbol : public Symbol, public Scope {
public:
    explicit DynamicScopeSymbol(const Scope& parent);

    /// Adds a symbol to the scope.
    void addSymbol(const Symbol& symbol);

    /// Creates one or more symbols for the given syntax node and adds them to the scope.
    /// Also returns the set of created symbols.
    SymbolList createAndAddSymbols(const SyntaxNode& node);

private:
    std::vector<const Symbol*> members;
};

/// This is a placeholder symbol for syntax nodes that need to defer evaluation until the
/// rest of the hierarchy is in place. Examples of this are generate nodes and hierarchy
/// instantiations. The parent scope will resolve the symbol and replace it in its own member
/// list on demand.
class LazySyntaxSymbol : public Symbol {
public:
    LazySyntaxSymbol(const SyntaxNode& syntax, const Scope& parent,
                     LazyDefinition* definition = nullptr);

    const Symbol* resolve() const;

private:
    const SyntaxNode& node;

    // If this lazy syntax is for a hierarchical instantiation, this member
    // will contain the set of shared data among all of the instances.
    LazyDefinition* instanceDefinition = nullptr;
};

/// The root of a single compilation unit.
class CompilationUnitSymbol : public Symbol, public Scope {
public:
    CompilationUnitSymbol(const Scope& parent);
};

/// A SystemVerilog package construct.
class PackageSymbol : public Symbol, public Scope {
public:
    PackageSymbol(string_view name, const Scope& parent);
};

/// Represents a module, interface, or program declaration.
class DefinitionSymbol : public Symbol, public Scope {
public:
    span<const ParameterSymbol* const> parameters;

    DefinitionSymbol(string_view name, const Scope& parent);

    static DefinitionSymbol& fromSyntax(SymbolFactory& factory, const ModuleDeclarationSyntax& syntax,
                                        const Scope& parent);

    void createParamOverrides(const ParameterValueAssignmentSyntax& syntax, ParamOverrideMap& map) const;
};

/// Base class for module, interface, and program instance symbols.
class InstanceSymbol : public Symbol, public Scope {
public:
    const DefinitionSymbol& definition;

    /// Constructs LazySyntaxSymbols for each instance in the given syntax node.
    static void lazyFromSyntax(SymbolFactory& factory, const HierarchyInstantiationSyntax& syntax,
                               const Scope& parent, SmallVector<const Symbol*>& results);

    static InstanceSymbol& fromSyntax(SymbolFactory& factory, const HierarchicalInstanceSyntax& syntax,
                                      const LazyDefinition& definition, const Scope& parent);

protected:
    InstanceSymbol(SymbolKind kind, string_view name, const DefinitionSymbol& definition, const Scope& parent);
};

class ModuleInstanceSymbol : public InstanceSymbol {
public:
    ModuleInstanceSymbol(string_view name, const DefinitionSymbol& definition, const Scope& parent);
};

//class GenvarSymbol : public Symbol {
//public:
//    GenvarSymbol(string_view name, SourceLocation location, ) :
//        Symbol(SymbolKind::Genvar, nullptr, name, location) {}
//};

class SequentialBlockSymbol : public Symbol, public Scope {
public:
    LazyStatement body;

    SequentialBlockSymbol(const Scope& parent);

    static SequentialBlockSymbol& createImplicitBlock(SymbolFactory& factory,
                                                      const ForLoopStatementSyntax& forLoop,
                                                      const Scope& parent);
};

class ProceduralBlockSymbol : public Symbol, public Scope {
public:
    LazyStatement body;
    ProceduralBlockKind procedureKind;

    ProceduralBlockSymbol(const Scope& parent, ProceduralBlockKind procedureKind);
};

/// Represents blocks that are instantiated by a loop generate or conditional
/// generate construct. These blocks can contain a bunch of members, or just
/// a single item. They can also contain an implicit parameter representing
/// the loop iteration value.
class GenerateBlockSymbol : public Symbol, public Scope {
public:
    GenerateBlockSymbol(string_view name, const Scope& parent);

    /// Creates a generate block from the given if-generate syntax node. Note that
    /// this can return null if the condition is false and there is no else block.
    static GenerateBlockSymbol* fromSyntax(SymbolFactory& factory, const IfGenerateSyntax& syntax,
                                           const Scope& parent);
};

/// Represents an array of generate blocks, as generated by a loop generate construct.
class GenerateBlockArraySymbol : public Symbol, public Scope {
public:
    GenerateBlockArraySymbol(string_view name, const Scope& parent);

    /// Creates a generate block array from the given loop-generate syntax node.
    static GenerateBlockArraySymbol& fromSyntax(SymbolFactory& factory, const LoopGenerateSyntax& syntax,
                                                const Scope& parent);
};

/// Represents an explicit import from a package. This symbol type is
/// special in that it won't be returned from a lookup() call; instead
/// it will be unwrapped into the imported symbol.
class ExplicitImportSymbol : public Symbol {
public:
    string_view packageName;
    string_view importName;

    ExplicitImportSymbol(string_view packageName, string_view importName,
                         SourceLocation location, const Scope& parent);

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

    WildcardImportSymbol(string_view packageName, SourceLocation location, const Scope& parent);

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

    ParameterSymbol(string_view name, const Scope& parent);

    static void fromSyntax(SymbolFactory& factory, const ParameterDeclarationSyntax& syntax,
                           const Scope& parent, SmallVector<ParameterSymbol*>& results);
};

/// Represents a variable declaration (which does not include nets).
class VariableSymbol : public Symbol {
public:
    LazyType type;
    LazyInitializer initializer;
    VariableLifetime lifetime;
    bool isConst;

    VariableSymbol(string_view name, const Scope& parent,
                   VariableLifetime lifetime = VariableLifetime::Automatic, bool isConst = false);

    /// Constructs all variable symbols specified by the given syntax node.
    static void fromSyntax(SymbolFactory& factory, const DataDeclarationSyntax& syntax,
                           const Scope& parent, SmallVector<const VariableSymbol*>& results);

protected:
    VariableSymbol(SymbolKind childKind, string_view name, const Scope& parent,
                   VariableLifetime lifetime = VariableLifetime::Automatic, bool isConst = false);
};

/// Represents a formal argument in subroutine (task or function).
class FormalArgumentSymbol : public VariableSymbol {
public:
    FormalArgumentDirection direction = FormalArgumentDirection::In;

    FormalArgumentSymbol(const Scope& parent);

    FormalArgumentSymbol(string_view name, const Scope& parent,
                         FormalArgumentDirection direction = FormalArgumentDirection::In);
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

    SubroutineSymbol(string_view name, VariableLifetime defaultLifetime, bool isTask, const Scope& parent);
    SubroutineSymbol(string_view name, SystemFunction systemFunction, const Scope& parent);

    static SubroutineSymbol& fromSyntax(SymbolFactory& factory, const FunctionDeclarationSyntax& syntax,
                                        const Scope& parent);

    bool isSystemFunction() const { return systemFunctionKind != SystemFunction::Unknown; }
};

}
