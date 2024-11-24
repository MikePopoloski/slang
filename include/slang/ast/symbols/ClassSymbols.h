//------------------------------------------------------------------------------
//! @file ClassSymbols.h
//! @brief Class-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Constraints.h"
#include "slang/ast/Scope.h"
#include "slang/ast/symbols/CompilationUnitSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Function.h"
#include "slang/util/Hash.h"

namespace slang::ast {

class ASTContext;
class Constraint;
class Expression;
class GenericClassDefSymbol;

class SLANG_EXPORT ClassPropertySymbol : public VariableSymbol {
public:
    Visibility visibility;
    RandMode randMode = RandMode::None;

    ClassPropertySymbol(std::string_view name, SourceLocation loc, VariableLifetime lifetime,
                        Visibility visibility);

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(const Scope& scope, const syntax::ClassPropertyDeclarationSyntax& syntax,
                           SmallVectorBase<const ClassPropertySymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClassProperty; }
};

/// Represents a class definition type.
class SLANG_EXPORT ClassType : public Type, public Scope {
public:
    /// If the class type was specialized from a generic class, this is
    /// a pointer to that generic class definition.
    const GenericClassDefSymbol* genericClass = nullptr;

    /// A variable that points to the instance of this class itself, which is
    /// used by non-static class property initializers that refers to the
    /// special "this" handle. Subroutines and constraint blocks have their
    /// own "thisVar" members.
    const VariableSymbol* thisVar = nullptr;

    /// Set to true if the class is an abstract class (declared with the
    /// "virtual" keyword).
    bool isAbstract = false;

    /// Set to true if the class is an interface class.
    bool isInterface = false;

    /// Set to true if this class is marked final (i.e. it cannot be extended).
    bool isFinal = false;

    ClassType(Compilation& compilation, std::string_view name, SourceLocation loc);

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
    std::span<const Type* const> getImplementedInterfaces() const {
        ensureElaborated();
        return implementsIfaces;
    }

    /// Gets the list of interface classes that this class implements, as declared
    /// in the class type declaration (i.e. it does not include any parent interfaces
    /// inherited from the ones in the declaration).
    /// If this class is itself an interface class, this is instead the list of
    /// interface classes that it extends from, if any.
    std::span<const Type* const> getDeclaredInterfaces() const {
        ensureElaborated();
        return declaredIfaces;
    }

    /// If this class has a base class with a constructor, gets the expression used to
    /// invoke that method. Otherwise returns nullptr.
    const Expression* getBaseConstructorCall() const;

    /// Gets the class constructor function, if it has an explicit constructor.
    /// Otherwise returns nullptr.
    const SubroutineSymbol* getConstructor() const;

    /// Gets $bits of the type. Returns zero if the type does not have a statically known size.
    uint64_t getBitstreamWidth() const {
        if (!cachedBitstreamWidth)
            computeSize();
        return *cachedBitstreamWidth;
    }

    /// Returns true if this class type has recursive cycles in its
    /// properties (i.e. properties with the same type as this class,
    /// directly or indirectly).
    bool hasCycles() const {
        if (!cachedHasCycles)
            computeCycles();
        return *cachedHasCycles;
    }

    static const Symbol& fromSyntax(const Scope& scope,
                                    const syntax::ClassDeclarationSyntax& syntax);

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

    void populate(const Scope& scope, const syntax::ClassDeclarationSyntax& syntax);
    void inheritMembers(function_ref<void(const Symbol&)> insertCB) const;
    void handleExtends(const syntax::ExtendsClauseSyntax& extendsClause, const ASTContext& context,
                       function_ref<void(const Symbol&)> insertCB) const;
    void handleImplements(const syntax::ImplementsClauseSyntax& implementsClause,
                          const ASTContext& context,
                          function_ref<void(const Symbol&)> insertCB) const;
    void computeSize() const;
    void computeCycles() const;

    mutable const Type* baseClass = nullptr;
    mutable const Symbol* baseConstructor = nullptr;
    mutable const ForwardingTypedefSymbol* firstForward = nullptr;
    mutable std::span<const Type* const> implementsIfaces;
    mutable std::span<const Type* const> declaredIfaces;
    mutable std::optional<const Expression*> baseConstructorCall;
    mutable std::optional<uint64_t> cachedBitstreamWidth;
    mutable std::optional<bool> cachedHasCycles;
    SymbolIndex headerIndex;
};

namespace detail {

// This would ideally be a private member of GenericClassDefSymbol but
// MSVC has a bug using the Hasher object in boost::unordered_flat_map
// when that's the case so it's separated here for now.
class ClassSpecializationKey {
public:
    ClassSpecializationKey(const GenericClassDefSymbol& def,
                           std::span<const ConstantValue* const> paramValues,
                           std::span<const Type* const> typeParams);

    size_t hash() const { return savedHash; }

    bool operator==(const ClassSpecializationKey& other) const;

private:
    const GenericClassDefSymbol* definition;
    std::span<const ConstantValue* const> paramValues;
    std::span<const Type* const> typeParams;
    size_t savedHash;
};

struct ClassSpecializationHasher {
    size_t operator()(const ClassSpecializationKey& key) const { return key.hash(); }
};

} // namespace detail

/// Represents a generic class definition, which is a parameterized class that has not
/// yet had its parameter values specified. This is a not a type -- the generic class
/// must first be specialized in order to be a type usable in expressions and declarations.
class SLANG_EXPORT GenericClassDefSymbol : public Symbol {
public:
    using SpecializeFunc = function_ref<void(Compilation&, ClassType&, SourceLocation)>;

    /// Set to true if the generic class is an interface class.
    bool isInterface = false;

    GenericClassDefSymbol(std::string_view name, SourceLocation loc) :
        Symbol(SymbolKind::GenericClassDef, name, loc) {}
    GenericClassDefSymbol(std::string_view name, SourceLocation loc,
                          SpecializeFunc specializeFunc) :
        Symbol(SymbolKind::GenericClassDef, name, loc), specializeFunc{specializeFunc} {}

    /// Gets the default specialization for the class, or nullptr if the generic
    /// class has no default specialization (because some parameters are not defaulted).
    const Type* getDefaultSpecialization() const;

    /// Gets the specialization for the class given the specified parameter value
    /// assignments. The result is cached and reused if requested more than once.
    const Type& getSpecialization(const ASTContext& context,
                                  const syntax::ParameterValueAssignmentSyntax& syntax) const;

    /// Forces a specialization with all parameters set to invalid values. This allows
    /// determining members that aren't dependent on parameters.
    const Type& getInvalidSpecialization() const;

    /// Gets the number of specializations that have been made for this generic class.
    size_t numSpecializations() const { return specMap.size(); }

    /// Gets an iterator to the specializations created for the generic class.
    auto specializations() const {
        return std::views::transform(specMap, [](auto& p) -> decltype(auto) { return *p.second; });
    }

    void addForwardDecl(const ForwardingTypedefSymbol& decl) const;
    const ForwardingTypedefSymbol* getFirstForwardDecl() const { return firstForward; }

    /// Checks all forward declarations for validity when considering the target type
    /// of this alias. Any inconsistencies will issue diagnostics.
    void checkForwardDecls() const;

    /// Adds a new parameter declaration to the generic class. This is only used for
    /// programmatically constructed generic classes (not sourced from syntax).
    /// Behavior is undefined if this generic class has already been instantiated and used.
    void addParameterDecl(const DefinitionSymbol::ParameterDecl& decl);

    void serializeTo(ASTSerializer& serializer) const;

    static const Symbol& fromSyntax(const Scope& scope,
                                    const syntax::ClassDeclarationSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::GenericClassDef; }

private:
    const Type* getSpecializationImpl(const ASTContext& context, SourceLocation instanceLoc,
                                      bool forceInvalidParams,
                                      const syntax::ParameterValueAssignmentSyntax* syntax) const;

    SmallVector<DefinitionSymbol::ParameterDecl, 8> paramDecls;

    using SpecMap = flat_hash_map<detail::ClassSpecializationKey, const Type*,
                                  detail::ClassSpecializationHasher>;
    mutable SpecMap specMap;
    mutable SpecMap uninstantiatedSpecMap;
    mutable std::optional<const Type*> defaultSpecialization;
    mutable const ForwardingTypedefSymbol* firstForward = nullptr;
    mutable uint32_t recursionDepth = 0;
    SpecializeFunc specializeFunc;
};

/// Specifies various flags that can apply to constraint bocks.
enum class SLANG_EXPORT ConstraintBlockFlags : uint8_t {
    /// No specific flags specified.
    None = 0,

    /// The constraint is 'pure', meaning it requires
    /// an implementation in derived classes.
    Pure = 1 << 1,

    /// The conbstraint is static, meaning it is shared across
    /// all object instances.
    Static = 1 << 2,

    /// The constraint block was declared extern, either
    /// implicitly or explicitly.
    Extern = 1 << 3,

    /// The constraint block was explicitly declared extern, which
    /// means an out-of-block body is required instead of optional.
    ExplicitExtern = 1 << 4,

    /// The constraint is marked 'initial', which means it should not
    /// override a base class constraint.
    Initial = 1 << 5,

    /// The constraint is marked 'extends', which means it must override
    /// a base class constraint.
    Extends = 1 << 6,

    /// The constraint is marked 'final', which means it cannot be
    /// overridden in a derived class.
    Final = 1 << 7
};
SLANG_BITMASK(ConstraintBlockFlags, Final)

/// Represents a named constraint block declaration within a class.
class SLANG_EXPORT ConstraintBlockSymbol : public Symbol, public Scope {
public:
    /// If this is a non-static constraint block, this is a variable
    /// that represents the 'this' class handle.
    const VariableSymbol* thisVar = nullptr;

    /// Various flags that control constraint block behavior.
    bitmask<ConstraintBlockFlags> flags;

    ConstraintBlockSymbol(Compilation& compilation, std::string_view name, SourceLocation loc);

    const Constraint& getConstraints() const;
    SymbolIndex getOutOfBlockIndex() const { return outOfBlockIndex; }

    void serializeTo(ASTSerializer& serializer) const;

    static ConstraintBlockSymbol* fromSyntax(const Scope& scope,
                                             const syntax::ConstraintDeclarationSyntax& syntax);

    static ConstraintBlockSymbol& fromSyntax(const Scope& scope,
                                             const syntax::ConstraintPrototypeSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ConstraintBlock; }

    template<typename TVisitor>
    void visitExprs(TVisitor&& visitor) const {
        getConstraints().visit(visitor);
    }

private:
    void addThisVar(const Type& type);

    mutable const Constraint* constraint = nullptr;
    mutable SymbolIndex outOfBlockIndex{0};
};

} // namespace slang::ast
