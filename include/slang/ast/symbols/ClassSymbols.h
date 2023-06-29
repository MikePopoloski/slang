//------------------------------------------------------------------------------
//! @file ClassSymbols.h
//! @brief Class-related symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Constraints.h"
#include "slang/ast/Definition.h"
#include "slang/ast/Scope.h"
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

    /// Set to true if the class is an abstract class (declared with the
    /// "virtual" keyword).
    bool isAbstract = false;

    /// Set to true if the class is an interface class.
    bool isInterface = false;

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

    mutable const Type* baseClass = nullptr;
    mutable const Symbol* baseConstructor = nullptr;
    mutable std::optional<const Expression*> baseConstructorCall;
    mutable const ForwardingTypedefSymbol* firstForward = nullptr;
    mutable std::span<const Type* const> implementsIfaces;
    mutable std::span<const Type* const> declaredIfaces;
    SymbolIndex headerIndex;
};

/// Represents a generic class definition, which is a parameterized class that has not
/// yet had its parameter values specified. This is a not a type -- the generic class
/// must first be specialized in order to be a type usable in expressions and declarations.
class SLANG_EXPORT GenericClassDefSymbol : public Symbol {
public:
    /// Set to true if the generic class is an interface class.
    bool isInterface = false;

    GenericClassDefSymbol(std::string_view name, SourceLocation loc) :
        Symbol(SymbolKind::GenericClassDef, name, loc) {}
    GenericClassDefSymbol(std::string_view name, SourceLocation loc,
                          function_ref<void(Compilation&, ClassType&)> specializeFunc) :
        Symbol(SymbolKind::GenericClassDef, name, loc),
        specializeFunc{specializeFunc} {}

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
    void addParameterDecl(const Definition::ParameterDecl& decl);

    void serializeTo(ASTSerializer& serializer) const;

    static const Symbol& fromSyntax(const Scope& scope,
                                    const syntax::ClassDeclarationSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::GenericClassDef; }

private:
    class SpecializationKey {
    public:
        SpecializationKey(const GenericClassDefSymbol& def,
                          std::span<const ConstantValue* const> paramValues,
                          std::span<const Type* const> typeParams);

        size_t hash() const { return savedHash; }

        bool operator==(const SpecializationKey& other) const;

    private:
        const GenericClassDefSymbol* definition;
        std::span<const ConstantValue* const> paramValues;
        std::span<const Type* const> typeParams;
        size_t savedHash;
    };

    struct Hasher {
        size_t operator()(const SpecializationKey& key) const { return key.hash(); }
    };

    const Type* getSpecializationImpl(const ASTContext& context, SourceLocation instanceLoc,
                                      bool forceInvalidParams,
                                      const syntax::ParameterValueAssignmentSyntax* syntax) const;

    SmallVector<Definition::ParameterDecl, 8> paramDecls;

    using SpecMap = flat_hash_map<SpecializationKey, const Type*, Hasher>;
    mutable SpecMap specMap;
    mutable std::optional<const Type*> defaultSpecialization;
    mutable const ForwardingTypedefSymbol* firstForward = nullptr;
    function_ref<void(Compilation&, ClassType&)> specializeFunc;
};

/// Represents a named constraint block declaration within a class.
class SLANG_EXPORT ConstraintBlockSymbol : public Symbol, public Scope {
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
