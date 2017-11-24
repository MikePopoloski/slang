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
#include "numeric/SVInt.h"
#include "parsing/AllSyntax.h"
#include "text/SourceLocation.h"
#include "util/HashMap.h"
#include "util/Iterator.h"

#include "ConstantValue.h"
#include "SemanticFacts.h"

namespace slang {

class DefinitionSymbol;
class Statement;
class StatementList;
class Expression;
class SyntaxTree;
class Symbol;
class ScopeSymbol;
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
    ImplicitImport,
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

/// Specifies possible kinds of lookups that can be done.
enum class LookupKind {
    /// A direct lookup within the scope is performed, with no upward name referencing
    /// allowed. The lookup location is only used for error reporting, not qualifying
    /// which signals are accessible. Package imports are not considered.
    Direct,

    /// A lookup of a simple name, starting in the local scope. The lookup location is
    /// used to qualify accessible signals. Package imports are considered.
    Local,

    /// The lookup is for the first part of a scoped name. This first performs
    /// the equivalent of a Local lookup; if no symbol is found using that method,
    /// it will search for a package with the given name.
    Scoped,

    /// A lookup for a simple name that is part of a callable expression (task or function).
    /// This is similar to a Local lookup, with additional rules specific to callables.
    Callable,

    /// A lookup for a module, interface, or program definition. Similar to a Callable lookup,
    /// there are additional rules about where definitions can be found.
    Definition
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

    /// The symbol that contains this symbol in the source text. All symbols have a containing
    /// symbol except for the design root, which has itself as the containing symbol. Keep that
    /// in mind when traversing the parent links.
    const ScopeSymbol* getParent() const { return parentScope; }

    /// Finds the first ancestor symbol of the given kind. If this symbol is already of
    /// the given kind, returns this symbol.
    const Symbol* findAncestor(SymbolKind searchKind) const;

    /// Gets the symbol for the root of the design.
    const RootSymbol& getRoot() const;

    SymbolFactory& getFactory() const;

    template<typename T>
    T& as() { return *static_cast<T*>(this); }

    template<typename T>
    const T& as() const { return *static_cast<const T*>(this); }

    /// Makes a clone of the symbol with the provided scope as the new parent.
    Symbol& clone(const ScopeSymbol& newParent) const;

    template<typename TDerived, typename TResult, typename TSource>
    struct Lazy {
        Lazy(const ScopeSymbol* scope, const TResult* init) : storedScope(scope), cache(init) {}
        Lazy(const ScopeSymbol* scope, const TSource& init) : storedScope(scope), cache(&init) {}

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
        const ScopeSymbol* storedScope;

    private:
        mutable std::variant<const TResult*, const TSource*> cache;
    };

    struct LazyConstant : public Lazy<LazyConstant, ConstantValue, ExpressionSyntax> {
        explicit LazyConstant(const ScopeSymbol* scope);
        LazyConstant(const ScopeSymbol* scope, const ConstantValue* init) :
            Lazy<LazyConstant, ConstantValue, ExpressionSyntax>(scope, init) {}
        LazyConstant(const ScopeSymbol* scope, const ExpressionSyntax& init) :
            Lazy<LazyConstant, ConstantValue, ExpressionSyntax>(scope, init) {}

        LazyConstant& operator=(const ExpressionSyntax& source);
        LazyConstant& operator=(ConstantValue result);

    private:
        friend struct Lazy<LazyConstant, ConstantValue, ExpressionSyntax>;
        const ConstantValue& evaluate(const ScopeSymbol& scope, const ExpressionSyntax& source) const;
    };

#define LAZY(name, TResult, TSource)                            \
    struct name : public Lazy<name, TResult, TSource> {         \
        explicit name(const ScopeSymbol* scope);                \
        name(const ScopeSymbol* scope, const TResult* init) :   \
            Lazy<name, TResult, TSource>(scope, init) {}        \
        name(const ScopeSymbol* scope, const TSource& init) :   \
            Lazy<name, TResult, TSource>(scope, init) {}        \
        using Lazy<name, TResult, TSource>::operator=;          \
    private:                                                    \
        friend struct Lazy<name, TResult, TSource>;             \
        const TResult& evaluate(const ScopeSymbol& scope, const TSource& source) const; \
    }

    LAZY(LazyStatement, Statement, StatementSyntax);
    LAZY(LazyStatementList, StatementList, SyntaxList<SyntaxNode>);
    LAZY(LazyInitializer, Expression, ExpressionSyntax);
    LAZY(LazyType, TypeSymbol, DataTypeSyntax);

    // TODO: move this stuff to its own header / namespace
    struct LazyDefinition {
        using Source = const HierarchyInstantiationSyntax*;
        using Value = std::tuple<const DefinitionSymbol*, ParamOverrideMap>;

        LazyDefinition(const ScopeSymbol* scope, Source source) : scope(scope), cache(source) {}
        const Value& get() const;

    private:
        const ScopeSymbol* scope;
        mutable std::variant<Value, Source> cache;
    };

#undef LAZY

protected:
    explicit Symbol(SymbolKind kind, string_view name = "", SourceLocation location = SourceLocation()) :
        kind(kind), name(name), location(location) {}

    Symbol(SymbolKind kind, const ScopeSymbol& containingSymbol, string_view name = "",
           SourceLocation location = SourceLocation()) :
        kind(kind), name(name), location(location),
        parentScope(&containingSymbol) {}

    Symbol(SymbolKind kind, Token token, const ScopeSymbol& containingSymbol) :
        kind(kind), name(token.valueText()), location(token.location()),
        parentScope(&containingSymbol) {}

    Diagnostic& addError(DiagCode code, SourceLocation location) const;

private:
    const ScopeSymbol* parentScope = nullptr;
};

/// Base class for symbols that also act as scopes, which means they contain
/// child symbols that can be looked up by name.
class ScopeSymbol : public Symbol {
public:
    /// Looks up a symbol in the current scope. Returns null if no symbol is found.
    ///
    /// @param lookupLocation is used for reporting errors if the symbol is not found.
    ///        Additionally, depending on the `lookupKind` being used, it may be used
    ///        to qualify which local symbols are accessible.
    /// @param lookupKind specifies the kind of lookup to perform. This controls which
    ///        symbols are accessible, whether package imports are considered, and
    ///        whether parent scopes should be included.
    ///
    const Symbol* lookup(string_view searchName, SourceLocation lookupLocation, LookupKind lookupKind) const;

    /// Looks up a symbol in the current scope, expecting it to exist and be of the
    /// given type. If those conditions do not hold, this will assert.
    template<typename T>
    const T& lookup(string_view name, SourceLocation lookupLocation = SourceLocation(),
                    LookupKind lookupKind = LookupKind::Direct) const {
        const Symbol* sym = lookup(name, lookupLocation, lookupKind);
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
    using Symbol::Symbol;

private:
    void buildNameMap() const;

    // The list of members assigned to this scope.
    span<const Symbol*> memberList;

    // The map of names to members that can be looked up within this scope. This is built
    // on demand the first time a name lookup is performed. This map can contain names from
    // symbols that are lexically in other scopes but have been made visible here, such
    // as with enum values and package imports.
    mutable SymbolMap* nameMap = nullptr;
};

/// A scope that can be dynamically modified programmatically. Not used for batch compilation; intended
/// for tools and unit tests.
class DynamicScopeSymbol : public ScopeSymbol {
public:
    explicit DynamicScopeSymbol(const ScopeSymbol& parent);

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
    LazySyntaxSymbol(const SyntaxNode& syntax, const ScopeSymbol& parent,
                     LazyDefinition* definition = nullptr);

    const Symbol* resolve() const;

private:
    const SyntaxNode& node;

    // If this lazy syntax is for a hierarchical instantiation, this member
    // will contain the set of shared data among all of the instances.
    LazyDefinition* instanceDefinition = nullptr;
};

/// The root of a single compilation unit.
class CompilationUnitSymbol : public ScopeSymbol {
public:
    CompilationUnitSymbol(const ScopeSymbol& parent);
};

/// A SystemVerilog package construct.
class PackageSymbol : public ScopeSymbol {
public:
    PackageSymbol(string_view name, const ScopeSymbol& parent);
};

/// Represents a module, interface, or program declaration.
class DefinitionSymbol : public ScopeSymbol {
public:
    span<const ParameterSymbol* const> parameters;

    DefinitionSymbol(string_view name, const ScopeSymbol& parent);

    static DefinitionSymbol& fromSyntax(SymbolFactory& factory, const ModuleDeclarationSyntax& syntax,
                                        const ScopeSymbol& parent);

    void createParamOverrides(const ParameterValueAssignmentSyntax& syntax, ParamOverrideMap& map) const;
};

/// Base class for module, interface, and program instance symbols.
class InstanceSymbol : public ScopeSymbol {
public:
    const DefinitionSymbol& definition;

    /// Constructs LazySyntaxSymbols for each instance in the given syntax node.
    static void lazyFromSyntax(SymbolFactory& factory, const HierarchyInstantiationSyntax& syntax,
                               const ScopeSymbol& parent, SmallVector<const Symbol*>& results);

    static InstanceSymbol& fromSyntax(SymbolFactory& factory, const HierarchicalInstanceSyntax& syntax,
                                      const LazyDefinition& definition, const ScopeSymbol& parent);

protected:
    InstanceSymbol(SymbolKind kind, string_view name, const DefinitionSymbol& definition, const ScopeSymbol& parent);
};

class ModuleInstanceSymbol : public InstanceSymbol {
public:
    ModuleInstanceSymbol(string_view name, const DefinitionSymbol& definition, const ScopeSymbol& parent);
};

//class GenvarSymbol : public Symbol {
//public:
//    GenvarSymbol(string_view name, SourceLocation location, ) :
//        Symbol(SymbolKind::Genvar, nullptr, name, location) {}
//};

class SequentialBlockSymbol : public ScopeSymbol {
public:
    LazyStatement body;

    SequentialBlockSymbol(const ScopeSymbol& parent);

    static SequentialBlockSymbol& createImplicitBlock(const ForLoopStatementSyntax& forLoop, const ScopeSymbol& parent);
};

class ProceduralBlockSymbol : public ScopeSymbol {
public:
    LazyStatement body;
    ProceduralBlockKind procedureKind;

    ProceduralBlockSymbol(const ScopeSymbol& parent, ProceduralBlockKind procedureKind);
};

/// Represents blocks that are instantiated by a loop generate or conditional
/// generate construct. These blocks can contain a bunch of members, or just
/// a single item. They can also contain an implicit parameter representing
/// the loop iteration value.
class GenerateBlockSymbol : public ScopeSymbol {
public:
    GenerateBlockSymbol(string_view name, const ScopeSymbol& parent);

    /// Creates a generate block from the given if-generate syntax node. Note that
    /// this can return null if the condition is false and there is no else block.
    static GenerateBlockSymbol* fromSyntax(SymbolFactory& factory, const IfGenerateSyntax& syntax,
                                           const ScopeSymbol& parent);
};

/// Represents an array of generate blocks, as generated by a loop generate construct.
class GenerateBlockArraySymbol : public ScopeSymbol {
public:
    GenerateBlockArraySymbol(string_view name, const ScopeSymbol& parent);

    /// Creates a generate block array from the given loop-generate syntax node.
    static GenerateBlockArraySymbol& fromSyntax(SymbolFactory& factory, const LoopGenerateSyntax& syntax,
                                                const ScopeSymbol& parent);
};

/// Represents an explicit import from a package. This symbol type is
/// special in that it won't be returned from a lookup() call; instead
/// it will be unwrapped into the imported symbol.
class ExplicitImportSymbol : public Symbol {
public:
    string_view packageName;
    string_view importName;

    ExplicitImportSymbol(string_view packageName, string_view importName,
                         SourceLocation location, const ScopeSymbol& parent);

    const PackageSymbol* package() const;
    const Symbol* importedSymbol() const;

private:
    mutable const PackageSymbol* package_ = nullptr;
    mutable const Symbol* import = nullptr;
    mutable bool initialized = false;
};

/// Represents a symbol that has been implicitly imported into a scope via
/// a wildcard import. This symbol type is special in that it won't be
/// returned from a lookup() call; also it is created on demand during
/// lookups of other symbols.
class ImplicitImportSymbol : public Symbol {
public:
    ImplicitImportSymbol(const WildcardImportSymbol& wildcard, const Symbol& importedSymbol,
                         const ScopeSymbol& parent);

    const WildcardImportSymbol& wildcard() const { return wildcard_; }
    const Symbol* importedSymbol() const { return &import; }
    const PackageSymbol* package() const;

private:
    const WildcardImportSymbol& wildcard_;
    const Symbol& import;
};

/// Represents a wildcard import declaration. This symbol is special in
/// that it won't be returned by a lookup, and won't even be in the name
/// map of a symbol at all. Instead there is a sideband list used to
/// resolve names via wildcard.
class WildcardImportSymbol : public Symbol {
public:
    string_view packageName;

    WildcardImportSymbol(string_view packageName, SourceLocation location, const ScopeSymbol& parent);

    const PackageSymbol* package() const;
    const ImplicitImportSymbol* resolve(string_view lookupName, SourceLocation lookupLocation) const;

private:
    mutable const PackageSymbol* package_ = nullptr;
    mutable bool initialized = false;
};

class ParameterSymbol : public Symbol {
public:
    LazyConstant defaultValue;
    LazyConstant value;
    bool isLocalParam = false;
    bool isPortParam = false;

    ParameterSymbol(string_view name, const ScopeSymbol& parent);

    static void fromSyntax(SymbolFactory& factory, const ParameterDeclarationSyntax& syntax,
                           const ScopeSymbol& parent, SmallVector<ParameterSymbol*>& results);
};

/// Represents a variable declaration (which does not include nets).
class VariableSymbol : public Symbol {
public:
    LazyType type;
    LazyInitializer initializer;
    VariableLifetime lifetime;
    bool isConst;

    VariableSymbol(string_view name, const ScopeSymbol& parent,
                   VariableLifetime lifetime = VariableLifetime::Automatic, bool isConst = false);

    /// Constructs all variable symbols specified by the given syntax node.
    static void fromSyntax(const ScopeSymbol& parent, const DataDeclarationSyntax& syntax,
                           SmallVector<const VariableSymbol*>& results);

protected:
    VariableSymbol(SymbolKind childKind, string_view name, const ScopeSymbol& parent,
                   VariableLifetime lifetime = VariableLifetime::Automatic, bool isConst = false);
};

/// Represents a formal argument in subroutine (task or function).
class FormalArgumentSymbol : public VariableSymbol {
public:
    FormalArgumentDirection direction = FormalArgumentDirection::In;

    FormalArgumentSymbol(const ScopeSymbol& parent);

    FormalArgumentSymbol(string_view name, const ScopeSymbol& parent,
                         FormalArgumentDirection direction = FormalArgumentDirection::In);
};

/// Represents a subroutine (task or function).
class SubroutineSymbol : public ScopeSymbol {
public:
    using ArgList = span<const FormalArgumentSymbol* const>;

    LazyStatementList body;
    LazyType returnType;
    ArgList arguments;
    VariableLifetime defaultLifetime = VariableLifetime::Automatic;
    SystemFunction systemFunctionKind = SystemFunction::Unknown;
    bool isTask = false;

    SubroutineSymbol(string_view name, VariableLifetime defaultLifetime, bool isTask, const ScopeSymbol& parent);
    SubroutineSymbol(string_view name, SystemFunction systemFunction, const ScopeSymbol& parent);

    static SubroutineSymbol& fromSyntax(SymbolFactory& factory, const FunctionDeclarationSyntax& syntax,
                                        const ScopeSymbol& parent);

    bool isSystemFunction() const { return systemFunctionKind != SystemFunction::Unknown; }
};

}
