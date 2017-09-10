//------------------------------------------------------------------------------
// Symbol.h
// Symbols for semantic analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "diagnostics/Diagnostics.h"
#include "numeric/SVInt.h"
#include "parsing/AllSyntax.h"
#include "text/SourceLocation.h"
#include "util/HashMap.h"

#include "ConstantValue.h"

namespace slang {

class BoundExpression;
class BoundStatement;
class BoundStatementList;
class SyntaxTree;
class Symbol;
class ScopeSymbol;
class DesignRootSymbol;
class TypeSymbol;
class ModuleSymbol;
class WildcardImportSymbol;
class PackageSymbol;

using SymbolList = span<const Symbol* const>;
using SymbolMap = std::unordered_map<string_view, const Symbol*>;

using Dimensions = span<ConstantRange const>;

enum class SymbolKind {
    Unknown,
    Root,
    DynamicScope,
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
    ParameterizedModule,
    Interface, // TODO: decouple interfaces from modules
    Modport,   // TODO: decouple interfaces from modules
    ModuleInstance,
    Package,
    ExplicitImport,
    ImplicitImport,
    WildcardImport,
    Program,
    Attribute,
    Genvar,
    GenerateBlock,
    ProceduralBlock,
    SequentialBlock,
    Variable,
    Instance,
    FormalArgument,
    Subroutine
};

/// Specifies the storage lifetime of a variable.
enum class VariableLifetime {
    Automatic,
    Static
};

/// Specifies behavior of an argument passed to a subroutine.
enum class FormalArgumentDirection {
    In,
    Out,
    InOut,
    Ref,
    ConstRef
};

/// Indicates which built-in system function is represented by a symbol.
enum class SystemFunction {
    Unknown,
    clog2,
    bits,
    left,
    right,
    low,
    high,
    size,
    increment
};

/// Specifies possible procedural block kinds.
enum class ProceduralBlockKind {
    Initial,
    Final,
    Always,
    AlwaysComb,
    AlwaysLatch,
    AlwaysFF
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

/// Interprets a keyword token as a variable lifetime value.
/// If the token is unset, returns the value `defaultIfUnset`.
VariableLifetime getLifetimeFromToken(Token token, VariableLifetime defaultIfUnset);

/// Create symbols from the given syntax node. Note that this does not add them to the parent scope;
/// the returned symbols are not part of any tree until you add them somewhere.
SymbolList createSymbols(const SyntaxNode& node, const ScopeSymbol& parent);

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
    const Symbol& containingSymbol;

    /// Finds the first ancestor symbol of the given kind. If this symbol is already of
    /// the given kind, returns this symbol.
    const Symbol* findAncestor(SymbolKind searchKind) const;

    /// Gets the first containing parent symbol that is also a scope. If this is
    /// the design root, returns itself.
    const ScopeSymbol& containingScope() const;

    /// Gets the symbol for the root of the design.
    const DesignRootSymbol& getRoot() const;

    template<typename T>
    const T& as() const { return *static_cast<const T*>(this); }

    Symbol(const Symbol&) = delete;
    Symbol& operator=(const Symbol&) = delete;

protected:
    explicit Symbol(SymbolKind kind, const Symbol& containingSymbol, string_view name = "",
                    SourceLocation location = SourceLocation()) :
        kind(kind), name(name), location(location),
        containingSymbol(containingSymbol) {}

    Symbol(SymbolKind kind, Token token, const Symbol& containingSymbol) :
        kind(kind), name(token.valueText()), location(token.location()),
        containingSymbol(containingSymbol) {}

    Diagnostic& addError(DiagCode code, SourceLocation location) const;

    template<typename T, typename... Args>
    T& allocate(Args&&... args) const;
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
    SymbolList members() const;

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

    /// A helper method to get a type symbol, using the current scope as context.
    const TypeSymbol& getType(const DataTypeSyntax& syntax) const;

protected:
    using Symbol::Symbol;

    void init() const;
    void addMember(const Symbol& symbol) const;

    // Derived classes override this to fill in members.
    virtual void initMembers() const {}

private:
    // For now, there is one hash table here for the normal members namespace. The other
    // namespaces are specific to certain symbol types so I don't want to have extra overhead
    // on every kind of scope symbol.
    mutable std::unordered_map<string_view, const Symbol*> memberMap;

    // In addition to the hash, also maintain an ordered list of members for easier access.
    mutable std::vector<const Symbol*> memberList;

    // Also, maintain a separate list containing just wildcard imports.
    // Every time we fail to look up a symbol name, we'll fall back to looking at imports.
    mutable std::vector<const WildcardImportSymbol*> wildcardImports;

    mutable bool membersInitialized = false;
};

/// A scope that can be dynamically modified programmatically. Not used for batch compilation; intended
/// for tools and unit tests.
class DynamicScopeSymbol : public ScopeSymbol {
public:
    explicit DynamicScopeSymbol(const Symbol& parent);

    /// Adds a symbol to the scope.
    void addSymbol(const Symbol& symbol);

    /// Creates one or more symbols for the given syntax node and adds them to the scope.
    /// Also returns the set of created symbols.
    SymbolList createAndAddSymbols(const SyntaxNode& node);
};

/// Base class for all data types.
class TypeSymbol : public Symbol {
public:
    TypeSymbol(SymbolKind kind, string_view name, const Symbol& parent) : Symbol(kind, parent, name) {}

    // SystemVerilog defines various levels of type compatibility, which are used
    // in different scenarios. See the spec, section 6.22.
    bool isMatching(const TypeSymbol& rhs) const;
    bool isEquivalent(const TypeSymbol& rhs) const;
    bool isAssignmentCompatible(const TypeSymbol& rhs) const;
    bool isCastCompatible(const TypeSymbol& rhs) const;

    // Helpers to get the following pieces of information for any type symbol,
    // though the information is stored differently for different types
    bool isSigned() const;
    bool isReal() const;
    bool isFourState() const;
    int width() const;

    std::string toString() const;

protected:
    using Symbol::Symbol;
};

class IntegralTypeSymbol : public TypeSymbol {
public:
    // a negative lower bound is actually an upper bound specified in the opposite order
    span<int const> lowerBounds;
    span<int const> widths;
    int width;
    TokenKind keywordType;
    bool isSigned;
    bool isFourState;

    IntegralTypeSymbol(TokenKind keywordType, int width, bool isSigned, bool isFourState, const Symbol& parent) :
        IntegralTypeSymbol(keywordType, width, isSigned, isFourState,
                           EmptyLowerBound, span<int const>(&width, 1), parent) {}

    IntegralTypeSymbol(TokenKind keywordType, int width, bool isSigned, bool isFourState,
                       span<int const> lowerBounds, span<int const> widths, const Symbol& parent) :
        TypeSymbol(SymbolKind::IntegralType, parent, getTokenKindText(keywordType), SourceLocation()),
        lowerBounds(lowerBounds), widths(widths),
        width(width), keywordType(keywordType), isSigned(isSigned), isFourState(isFourState) {}

private:
    static span<int const> EmptyLowerBound;
};

class RealTypeSymbol : public TypeSymbol {
public:
    int width;
    TokenKind keywordType;

    RealTypeSymbol(TokenKind keywordType, int width, const Symbol& parent) :
        TypeSymbol(SymbolKind::RealType, parent, getTokenKindText(keywordType), SourceLocation()),
        width(width), keywordType(keywordType) {}
};

//class EnumValueSymbol : public ConstValueSymbol {
//public:
//    EnumValueSymbol(string_view name, SourceLocation location, const TypeSymbol *type, ConstantValue val) :
//        ConstValueSymbol(SymbolKind::EnumValue, name, location, type, val) {}
//};
//
//class EnumTypeSymbol : public TypeSymbol {
//public:
//    const IntegralTypeSymbol* baseType;
//    span<EnumValueSymbol * const> values;
//
//    EnumTypeSymbol(const IntegralTypeSymbol *baseType, SourceLocation location, span<EnumValueSymbol * const> values) :
//        TypeSymbol(SymbolKind::EnumType, "", location),
//        baseType(baseType), values(values) {}
//};

class StructTypeSymbol : public TypeSymbol {
public:
    bool isPacked;
    bool isSigned;
};

/// An empty type symbol that indicates an error occurred while trying to
/// resolve the type of some expression or declaration.
class ErrorTypeSymbol : public TypeSymbol {
public:
    explicit ErrorTypeSymbol(const Symbol& parent) : TypeSymbol(SymbolKind::Unknown, parent) {}
};

class TypeAliasSymbol : public TypeSymbol {
public:
    const SyntaxNode& syntax;
    const TypeSymbol* underlying;

    TypeAliasSymbol(const SyntaxNode& syntax, SourceLocation location, const TypeSymbol* underlying, string_view alias, const Symbol& parent) :
        TypeSymbol(SymbolKind::TypeAlias, parent, alias, location),
        syntax(syntax), underlying(underlying) {}
};

class CompilationUnitSymbol;
class PackageSymbol;
class ParameterizedModuleSymbol;
class ModuleInstanceSymbol;

/// Represents the entirety of a design, along with all contained compilation units.
/// It also contains most of the machinery for creating and retrieving type symbols.
class DesignRootSymbol : public ScopeSymbol {
public:
    explicit DesignRootSymbol(const SourceManager& sourceManager);
    explicit DesignRootSymbol(const SyntaxTree* tree);
    explicit DesignRootSymbol(span<const SyntaxTree* const> trees);
    DesignRootSymbol(const SourceManager& sourceManager, span<const CompilationUnitSyntax* const> units);

    /// Gets all of the compilation units in the design.
    span<const CompilationUnitSymbol* const> compilationUnits() const { return unitList; }

    /// Finds all of the top-level module instances in the design. These form the roots of the
    /// actual design hierarchy.
    span<const ModuleInstanceSymbol* const> topInstances() const { init(); return topList; }

    /// Finds a package in the design with the given name, or returns null if none is found.
    const PackageSymbol* findPackage(string_view name) const;

    /// Methods for getting various type symbols.
    const TypeSymbol& getType(const DataTypeSyntax& syntax) const;
    const TypeSymbol& getType(const DataTypeSyntax& syntax, const ScopeSymbol& scope) const;
    const TypeSymbol& getKnownType(SyntaxKind kind) const;
    const TypeSymbol& getIntegralType(int width, bool isSigned, bool isFourState = true, bool isReg = false) const;
    const TypeSymbol& getErrorType() const;

    /// Report an error at the specified location.
    Diagnostic& addError(DiagCode code, SourceLocation location_) const {
        return diags.add(code, location_);
    }

    /// Allocate an object using the design's shared allocator.
    template<typename T, typename... Args>
    T& allocate(Args&&... args) const {
        return *alloc.emplace<T>(std::forward<Args>(args)...);
    }

    BumpAllocator& allocator() const { return alloc; }
    Diagnostics& diagnostics() const { return diags; }
    const SourceManager& sourceManager() const { return sourceMan; }

private:
    void initMembers() const final;

    // Gets a type symbol for the given integer type syntax node.
    const TypeSymbol& getIntegralType(const IntegerTypeSyntax& syntax, const ScopeSymbol& scope) const;

    // Evalutes variable dimensions that are expected to be compile-time constant.
    // Returns true if evaluation was successful; returns false and reports errors if not.
    bool evaluateConstantDims(const SyntaxList<VariableDimensionSyntax>& dimensions, SmallVector<ConstantRange>& results, const ScopeSymbol& scope) const;

    // Add a compilation unit to the design; has some shared code to filter out members of the compilation
    // unit that belong in the root scope (for example, modules).
    void addCompilationUnit(const CompilationUnitSymbol& unit);

    // These functions are used for traversing the syntax hierarchy and finding all instantiations.
    using NameSet = std::unordered_set<string_view>;
    static void findInstantiations(const ModuleDeclarationSyntax& module, std::vector<NameSet>& scopeStack,
                                   NameSet& found);
    static void findInstantiations(const MemberSyntax& node, std::vector<NameSet>& scopeStack, NameSet& found);

    // The name map for packages. Note that packages have their own namespace,
    // which is why they can't share the root name table.
    SymbolMap packageMap;

    // list of compilation units in the design
    std::vector<const CompilationUnitSymbol*> unitList;

    // preallocated type symbols for known types
    std::unordered_map<SyntaxKind, const TypeSymbol*> knownTypes;

    // These are mutable so that the design root can be logically const, observing
    // members lazily but allocating them on demand and reporting errors when asked.
    mutable BumpAllocator alloc;
    mutable Diagnostics diags;

    // list of top level module instances in the design
    mutable std::vector<const ModuleInstanceSymbol*> topList;

    // cache of simple integral types keyed by {width, signedness, 4-state, isReg}
    mutable std::unordered_map<uint64_t, const TypeSymbol*> integralTypeCache;

    const SourceManager& sourceMan;
};

/// The root of a single compilation unit.
class CompilationUnitSymbol : public ScopeSymbol {
public:
    CompilationUnitSymbol(const CompilationUnitSyntax& syntax, const Symbol& parent);
    CompilationUnitSymbol(SymbolList symbols, const Symbol& parent);
};

/// A SystemVerilog package construct.
class PackageSymbol : public ScopeSymbol {
public:
    PackageSymbol(const ModuleDeclarationSyntax& package, const Symbol& parent);

private:
    void initMembers() const final;

    const ModuleDeclarationSyntax& syntax;
};

/// Represents a module declaration, with its parameters still unresolved.
class ModuleSymbol : public Symbol {
public:
    const ModuleDeclarationSyntax& syntax;

    ModuleSymbol(const ModuleDeclarationSyntax& decl, const Symbol& container);

    /// Parameterizes the module with the given set of parameter assignments.
    const ParameterizedModuleSymbol& parameterize(const ParameterValueAssignmentSyntax* assignments = nullptr,
                                                  const ScopeSymbol* instanceScope = nullptr) const;

private:
    // Small collection of info extracted from a parameter definition
    struct ParameterInfo {
        const ParameterDeclarationSyntax& paramDecl;
        const VariableDeclaratorSyntax& declarator;
        string_view name;
        SourceLocation location;
        ExpressionSyntax* initializer;
        bool local;
        bool bodyParam;
    };

    const std::vector<ParameterInfo>& getDeclaredParams() const;
    ConstantValue evaluate(const ParameterDeclarationSyntax& paramDecl, const ScopeSymbol& scope,
                           const ExpressionSyntax& expr, SourceLocation declLocation) const;

    // Helper function used by getModuleParams to convert a single parameter declaration into
    // one or more ParameterInfo instances.
    bool getParamDecls(const ParameterDeclarationSyntax& syntax, std::vector<ParameterInfo>& buffer,
                       HashMapBase<string_view, SourceLocation>& nameDupMap,
                       bool lastLocal, bool overrideLocal, bool bodyParam) const;

    mutable std::optional<std::vector<ParameterInfo>> paramInfoCache;
};

/// Represents a module that has had its parameters resolved to a specific set of values.
class ParameterizedModuleSymbol : public ScopeSymbol {
public:
    ParameterizedModuleSymbol(const ModuleSymbol& module, const Symbol& parent,
                              const HashMapBase<string_view, ConstantValue>& parameterAssignments);

private:
    void initMembers() const final;

    const ModuleSymbol& module;
    std::unordered_map<string_view, ConstantValue> paramAssignments;
};

class ModuleInstanceSymbol : public Symbol {
public:
    const ParameterizedModuleSymbol& module;

    ModuleInstanceSymbol(string_view name, SourceLocation location, const ParameterizedModuleSymbol& module,
                         const Symbol& parent);

    /// A helper method to access a specific member of the module (of which this is an instance).
    template<typename T>
    const T& member(uint32_t index) const { return module.members()[index]->as<T>(); }
};

//class GenvarSymbol : public Symbol {
//public:
//    GenvarSymbol(string_view name, SourceLocation location, ) :
//        Symbol(SymbolKind::Genvar, nullptr, name, location) {}
//};

/// Base class for block scopes that can contain statements. This just lets us share some helper methods
/// for binding statements and creating local members.
class StatementBlockSymbol : public ScopeSymbol {
public:
    /// Binds a single statement.
    const BoundStatement& bindStatement(const StatementSyntax& syntax);

    /// Binds a list of statements, such as in a function body.
    const BoundStatementList& bindStatementList(const SyntaxList<SyntaxNode>& items);

protected:
    using ScopeSymbol::ScopeSymbol;

    const BoundStatement& bindStatement(const StatementSyntax& syntax) const;
    const BoundStatementList& bindStatementList(const SyntaxList<SyntaxNode>& items) const;

private:
    BoundStatement& bindReturnStatement(const ReturnStatementSyntax& syntax) const;
    BoundStatement& bindConditionalStatement(const ConditionalStatementSyntax& syntax) const;
    BoundStatement& bindForLoopStatement(const ForLoopStatementSyntax& syntax) const;
    BoundStatement& bindExpressionStatement(const ExpressionStatementSyntax& syntax) const;

    BoundStatement& badStmt(const BoundStatement* stmt) const;

    void bindVariableDecl(const DataDeclarationSyntax& syntax, SmallVector<const BoundStatement*>& results) const;
};

class SequentialBlockSymbol : public StatementBlockSymbol {
public:
    SequentialBlockSymbol(const Symbol& parent);

    const BoundStatement& getBody() const { ASSERT(body); return *body; }
    void setBody(const BoundStatement& statement) { body = &statement; }

private:
    const BoundStatement* body = nullptr;
};

class ProceduralBlockSymbol : public StatementBlockSymbol {
public:
    ProceduralBlockKind procedureKind;

    ProceduralBlockSymbol(const ProceduralBlockSyntax& syntax, const Symbol& parent);

    const BoundStatement& getBody() const { init(); ASSERT(body); return *body; }

private:
    void initMembers() const final;

    const ProceduralBlockSyntax& syntax;
    mutable const BoundStatement* body = nullptr;
};

/// Represents blocks that are instantiated by a loop generate or conditional
/// generate construct. These blocks can contain a bunch of members, or just
/// a single item. They can also contain an implicit parameter representing
/// the loop iteration value.
class GenerateBlockSymbol : public ScopeSymbol {
public:
    GenerateBlockSymbol(string_view name, SourceLocation location, const Symbol& parent);

    static void fromSyntax(const ScopeSymbol& parent, const IfGenerateSyntax& syntax,
                           SmallVector<const GenerateBlockSymbol*>& results);
    static void fromSyntax(const ScopeSymbol& parent, const LoopGenerateSyntax& syntax,
                           SmallVector<const GenerateBlockSymbol*>& results);

private:
    void initMembers() const final;
    void handleBlock(const SyntaxNode& syntax);

    const GenerateBlockSyntax* syntax = nullptr;
};

/// Represents an explicit import from a package. This symbol type is
/// special in that it won't be returned from a lookup() call; instead
/// it will be unwrapped into the imported symbol.
class ExplicitImportSymbol : public Symbol {
public:
    string_view packageName;
    string_view importName;

    ExplicitImportSymbol(string_view packageName, string_view importName,
                         SourceLocation location, const Symbol& parent);

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
                         const Symbol& parent);

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

    WildcardImportSymbol(string_view packageName, SourceLocation location, const Symbol& parent);

    const PackageSymbol* package() const;
    const ImplicitImportSymbol* resolve(string_view lookupName, SourceLocation lookupLocation) const;

private:
    mutable const PackageSymbol* package_ = nullptr;
    mutable bool initialized = false;
};

class ParameterSymbol : public Symbol {
public:
    ParameterSymbol(string_view name, SourceLocation location, const TypeSymbol& type,
                    const ConstantValue& value, const Symbol& parent);

    ParameterSymbol(string_view name, SourceLocation location, const TypeSymbol& type,
                    ConstantValue&& value, const Symbol& parent);

    const TypeSymbol& type() const { return *type_; }
    const ConstantValue& value() const { return value_; }

private:
    mutable const TypeSymbol* type_;
    mutable ConstantValue value_;
};

/// Represents a variable declaration (which does not include nets).
class VariableSymbol : public Symbol {
public:
    VariableLifetime lifetime;
    bool isConst;

    VariableSymbol(Token name, const DataTypeSyntax& type, const Symbol& parent, VariableLifetime lifetime,
                   bool isConst, const ExpressionSyntax* initializer);

    VariableSymbol(string_view name, SourceLocation location, const TypeSymbol& type, const Symbol& parent,
                   VariableLifetime lifetime = VariableLifetime::Automatic, bool isConst = false,
                   const BoundExpression* initializer = nullptr);

    /// Constructs all variable symbols specified by the given syntax node.
    static void fromSyntax(const Symbol& parent, const DataDeclarationSyntax& syntax,
                           SmallVector<const VariableSymbol*>& results);

    const TypeSymbol& type() const;
    const BoundExpression* initializer() const;

protected:
    VariableSymbol(SymbolKind childKind, string_view name, SourceLocation location, const TypeSymbol& type, const Symbol& parent,
                   VariableLifetime lifetime = VariableLifetime::Automatic, bool isConst = false,
                   const BoundExpression* initializer = nullptr);

private:
    // To allow lazy binding, save pointers to the raw syntax nodes. When we eventually bind,
    // we will fill in the type symbol and bound initializer. Also a user can fill in those
    // manually for synthetically constructed symbols.
    const DataTypeSyntax* typeSyntax = nullptr;
    const ExpressionSyntax* initializerSyntax = nullptr;
    mutable const TypeSymbol* typeSymbol = nullptr;
    mutable const BoundExpression* initializerBound = nullptr;
};

/// Represents a formal argument in subroutine (task or function).
class FormalArgumentSymbol : public VariableSymbol {
public:
    FormalArgumentDirection direction = FormalArgumentDirection::In;

    FormalArgumentSymbol(const TypeSymbol& type, const Symbol& parent);

    FormalArgumentSymbol(string_view name, SourceLocation location, const TypeSymbol& type, const Symbol& parent,
                         const BoundExpression* initializer = nullptr,
                         FormalArgumentDirection direction = FormalArgumentDirection::In);
};

/// Represents a subroutine (task or function.
class SubroutineSymbol : public StatementBlockSymbol {
public:
    const FunctionDeclarationSyntax* syntax = nullptr;
    VariableLifetime defaultLifetime = VariableLifetime::Automatic;
    SystemFunction systemFunctionKind = SystemFunction::Unknown;
    bool isTask = false;

    SubroutineSymbol(const FunctionDeclarationSyntax& syntax, const Symbol& parent);
    SubroutineSymbol(string_view name, const TypeSymbol& returnType, span<const FormalArgumentSymbol* const> arguments,
                     SystemFunction systemFunction, const Symbol& parent);

    const TypeSymbol& returnType() const { init(); return *returnType_; }
    const BoundStatementList& body() const { init(); return *body_; }
    span<const FormalArgumentSymbol* const> arguments() const { init(); return arguments_; }

    bool isSystemFunction() const { return systemFunctionKind != SystemFunction::Unknown; }

private:
    void initMembers() const final;

    mutable const TypeSymbol* returnType_ = nullptr;
    mutable const BoundStatementList* body_ = nullptr;
    mutable span<const FormalArgumentSymbol* const> arguments_;
};

template<typename T, typename... Args>
T& Symbol::allocate(Args&&... args) const {
    return getRoot().allocate<T>(std::forward<Args>(args)...);
}

}
