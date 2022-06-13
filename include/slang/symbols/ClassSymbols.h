//------------------------------------------------------------------------------
//! @file ClassSymbols.h
//! @brief Class-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/compilation/Definition.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/types/Type.h"
#include "slang/util/Function.h"
#include "slang/util/Hash.h"

namespace slang {

class BindContext;
class Constraint;
struct ClassPropertyDeclarationSyntax;

class ClassPropertySymbol : public VariableSymbol {
public:
    Visibility visibility;
    RandMode randMode = RandMode::None;

    ClassPropertySymbol(string_view name, SourceLocation loc, VariableLifetime lifetime,
                        Visibility visibility);

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(const Scope& scope, const ClassPropertyDeclarationSyntax& syntax,
                           SmallVector<const ClassPropertySymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClassProperty; }
};

class Expression;
class GenericClassDefSymbol;
struct ClassDeclarationSyntax;
struct ExtendsClauseSyntax;
struct ImplementsClauseSyntax;

/// Represents a class definition type.
class ClassType : public Type, public Scope {
public:
    /// If the class type was specialized from a generic class, this is
    /// a pointer to that generic class definition.
    const GenericClassDefSymbol* genericClass = nullptr;

    /// Set to true if the class is an abstract class (declared with the
    /// "virtual" keyword).
    bool isAbstract = false;

    /// Set to true if the class is an interface class.
    bool isInterface = false;

    ClassType(Compilation& compilation, string_view name, SourceLocation loc);

    /// If this class derives from a base class, returns that type. Otherwise returns null.
    const Type* getBaseClass() const {
        ensureElaborated();
        return baseClass;
    }

    /// Gets the list of interface classes that this class implements.
    /// If this class is itself an interface class, this is instead the list of
    /// interface classes that it extends from, if any.
    ///
    /// Note that this list is flattened from the full set of all interfaces implemented
    /// by any base classes or interface class parents, up the inheritance hierarchy.
    span<const Type* const> getImplementedInterfaces() const {
        ensureElaborated();
        return implementsIfaces;
    }

    /// If this class has a base class with a constructor, gets the expression used to
    /// invoke that method. Otherwise returns nullptr.
    const Expression* getBaseConstructorCall() const;

    static const Symbol& fromSyntax(const Scope& scope, const ClassDeclarationSyntax& syntax);

    void addForwardDecl(const ForwardingTypedefSymbol& decl) const;
    const ForwardingTypedefSymbol* getFirstForwardDecl() const { return firstForward; }

    /// Checks all forward declarations for validity when considering the target type
    /// of this alias. Any inconsistencies will issue diagnostics.
    void checkForwardDecls() const;

    ConstantValue getDefaultValueImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClassType; }

private:
    friend class Scope;
    friend class GenericClassDefSymbol;

    void populate(const Scope& scope, const ClassDeclarationSyntax& syntax);
    void inheritMembers(function_ref<void(const Symbol&)> insertCB) const;
    void handleExtends(const ExtendsClauseSyntax& extendsClause, const BindContext& context,
                       function_ref<void(const Symbol&)> insertCB) const;
    void handleImplements(const ImplementsClauseSyntax& implementsClause,
                          const BindContext& context,
                          function_ref<void(const Symbol&)> insertCB) const;

    mutable const Type* baseClass = nullptr;
    mutable const Symbol* baseConstructor = nullptr;
    mutable optional<const Expression*> baseConstructorCall;
    mutable const ForwardingTypedefSymbol* firstForward = nullptr;
    mutable span<const Type* const> implementsIfaces;
    SymbolIndex headerIndex;
};

struct ParameterValueAssignmentSyntax;

/// Represents a generic class definition, which is a parameterized class that has not
/// yet had its parameter values specified. This is a not a type -- the generic class
/// must first be specialized in order to be a type usable in expressions and declarations.
class GenericClassDefSymbol : public Symbol {
public:
    /// Set to true if the generic class is an interface class.
    bool isInterface = false;

    GenericClassDefSymbol(string_view name, SourceLocation loc) :
        Symbol(SymbolKind::GenericClassDef, name, loc) {}
    GenericClassDefSymbol(string_view name, SourceLocation loc,
                          function_ref<void(Compilation&, ClassType&)> specializeFunc) :
        Symbol(SymbolKind::GenericClassDef, name, loc),
        specializeFunc{ specializeFunc } {}

    /// Gets the default specialization for the class, or nullptr if the generic
    /// class has no default specialization (because some parameters are not defaulted).
    const Type* getDefaultSpecialization() const;

    /// Gets the specialization for the class given the specified parameter value
    /// assignments. The result is cached and reused if requested more than once.
    const Type& getSpecialization(const BindContext& context,
                                  const ParameterValueAssignmentSyntax& syntax) const;

    /// Forces a specialization with all parameters set to invalid values. This allows
    /// determining members that aren't dependent on parameters.
    const Type& getInvalidSpecialization() const;

    /// Gets the number of specializations that have been made for this generic class.
    size_t numSpecializations() const { return specMap.size(); }

    void addForwardDecl(const ForwardingTypedefSymbol& decl) const;
    const ForwardingTypedefSymbol* getFirstForwardDecl() const { return firstForward; }

    /// Checks all forward declarations for validity when considering the target type
    /// of this alias. Any inconsistencies will issue diagnostics.
    void checkForwardDecls() const;

    /// Adds a new parameter declaration to the generic class. This is only used for
    /// programmatically constructed generic classes (not sourced from syntax).
    /// Behavior is undefined if this generic class has already been instantiated and used.
    void addParameterDecl(const Definition::ParameterDecl& decl);

    void serializeTo(ASTSerializer& serializer) const;

    static const Symbol& fromSyntax(const Scope& scope, const ClassDeclarationSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::GenericClassDef; }

private:
    class SpecializationKey {
    public:
        SpecializationKey(const GenericClassDefSymbol& def,
                          span<const ConstantValue* const> paramValues,
                          span<const Type* const> typeParams);

        size_t hash() const { return savedHash; }

        bool operator==(const SpecializationKey& other) const;
        bool operator!=(const SpecializationKey& other) const { return !(*this == other); }

    private:
        const GenericClassDefSymbol* definition;
        span<const ConstantValue* const> paramValues;
        span<const Type* const> typeParams;
        size_t savedHash;
    };

    struct Hasher {
        size_t operator()(const SpecializationKey& key) const { return key.hash(); }
    };

    const Type* getSpecializationImpl(const BindContext& context, SourceLocation instanceLoc,
                                      bool forceInvalidParams,
                                      const ParameterValueAssignmentSyntax* syntax) const;

    SmallVectorSized<Definition::ParameterDecl, 8> paramDecls;

    using SpecMap = flat_hash_map<SpecializationKey, const Type*, Hasher>;
    mutable SpecMap specMap;
    mutable optional<const Type*> defaultSpecialization;
    mutable const ForwardingTypedefSymbol* firstForward = nullptr;
    function_ref<void(Compilation&, ClassType&)> specializeFunc;

public:
    /// An iterator for specializations of the generic class.
    class iterator : public iterator_facade<iterator, std::forward_iterator_tag, const Type> {
    public:
        iterator(SpecMap::const_iterator it) : it(it) {}
        iterator(const iterator& other) : it(other.it) {}

        iterator& operator=(const iterator& other) {
            it = other.it;
            return *this;
        }

        bool operator==(const iterator& other) const { return it == other.it; }

        const Type& operator*() const { return *it->second; }
        const Type& operator*() { return *it->second; }

        iterator& operator++() {
            ++it;
            return *this;
        }

        iterator operator++(int) {
            iterator tmp = *this;
            ++(*this);
            return tmp;
        }

    private:
        SpecMap::const_iterator it;
    };

    /// Gets an iterator to the specializations created for the generic class.
    iterator_range<iterator> specializations() const {
        return { iterator(specMap.begin()), iterator(specMap.end()) };
    }
};

struct ConstraintDeclarationSyntax;
struct ConstraintPrototypeSyntax;

/// Represents a named constraint block declaration within a class.
class ConstraintBlockSymbol : public Symbol, public Scope {
public:
    /// If this is a non-static constraint block, this is a variable
    /// that represents the 'this' class handle.
    const VariableSymbol* thisVar = nullptr;

    /// Set to true if this is a static constraint block.
    bool isStatic = false;

    /// Set to true if this constraint block was declared extern, either
    /// implicitly or explicitly.
    bool isExtern = false;

    /// Set to true if this constraint block was explicitly declared extern,
    /// which means an out-of-block body is required instead of optional.
    bool isExplicitExtern = false;

    /// Set to true if this is a 'pure' constraint block, once which is
    /// required to be overridden in derived classes.
    bool isPure = false;

    ConstraintBlockSymbol(Compilation& compilation, string_view name, SourceLocation loc);

    const Constraint& getConstraints() const;
    SymbolIndex getOutOfBlockIndex() const { return outOfBlockIndex; }

    void serializeTo(ASTSerializer& serializer) const;

    static ConstraintBlockSymbol* fromSyntax(const Scope& scope,
                                             const ConstraintDeclarationSyntax& syntax);

    static ConstraintBlockSymbol& fromSyntax(const Scope& scope,
                                             const ConstraintPrototypeSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ConstraintBlock; }

private:
    void addThisVar(const Type& type);

    mutable const Constraint* constraint = nullptr;
    mutable SymbolIndex outOfBlockIndex{ 0 };
};

} // namespace slang
