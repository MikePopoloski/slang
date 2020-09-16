//------------------------------------------------------------------------------
//! @file ClassSymbols.h
//! @brief Class-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>

#include "slang/compilation/Definition.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Type.h"
#include "slang/symbols/VariableSymbols.h"

namespace slang {

struct ClassPropertyDeclarationSyntax;

class ClassPropertySymbol : public VariableSymbol {
public:
    Visibility visibility;

    ClassPropertySymbol(string_view name, SourceLocation loc, VariableLifetime lifetime,
                        Visibility visibility);

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(const Scope& scope, const ClassPropertyDeclarationSyntax& syntax,
                           SmallVector<const ClassPropertySymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClassProperty; }
};

struct ClassMethodPrototypeSyntax;

class ClassMethodPrototypeSymbol : public Symbol, public Scope {
public:
    DeclaredType declaredReturnType;
    span<const FormalArgumentSymbol* const> arguments;
    SubroutineKind subroutineKind;
    Visibility visibility;
    bitmask<MethodFlags> flags;

    ClassMethodPrototypeSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                               SubroutineKind subroutineKind, Visibility visibility,
                               bitmask<MethodFlags> flags);

    const Type& getReturnType() const { return declaredReturnType.getType(); }
    const SubroutineSymbol* getSubroutine() const;

    void serializeTo(ASTSerializer& serializer) const;

    static ClassMethodPrototypeSymbol& fromSyntax(const Scope& scope,
                                                  const ClassMethodPrototypeSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClassMethodPrototype; }

private:
    mutable optional<const SubroutineSymbol*> subroutine;
};

class GenericClassDefSymbol;
struct ClassDeclarationSyntax;

/// Represents a class definition type.
class ClassType : public Type, public Scope {
public:
    /// If the class type was specialized from a generic class, this is
    /// a pointer to that generic class definition.
    const GenericClassDefSymbol* genericClass = nullptr;

    ClassType(Compilation& compilation, string_view name, SourceLocation loc);

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
    friend class GenericClassDefSymbol;

    const Type& populate(const Scope& scope, const ClassDeclarationSyntax& syntax);

    mutable const ForwardingTypedefSymbol* firstForward = nullptr;
};

struct ParameterValueAssignmentSyntax;

/// Represents a generic class definition, which is a parameterized class that has not
/// yet had its parameter values specified. This is a not a type -- the generic class
/// must first be specialized in order to be a type usable in expressions and declarations.
class GenericClassDefSymbol : public Symbol {
public:
    GenericClassDefSymbol(string_view name, SourceLocation loc) :
        Symbol(SymbolKind::GenericClassDef, name, loc) {}

    /// Gets the default specialization for the class, or nullptr if the generic
    /// class has no default specialization (because some parameters are not defaulted).
    const Type* getDefaultSpecialization(Compilation& compilation) const;

    /// Gets the specialization for the class given the specified parameter value
    /// assignments. The result is cached and reused if requested more than once.
    const Type& getSpecialization(Compilation& compilation, LookupLocation lookupLocation,
                                  const ParameterValueAssignmentSyntax& syntax) const;

    /// Forces a specialization with all parameters set to invalid values. This allows
    /// determining members that aren't dependent on parameters.
    const Type& getInvalidSpecialization(Compilation& compilation) const;

    /// Gets the number of specializations that have been made for this generic class.
    size_t numSpecializations() const { return specMap.size(); }

    void addForwardDecl(const ForwardingTypedefSymbol& decl) const;
    const ForwardingTypedefSymbol* getFirstForwardDecl() const { return firstForward; }

    /// Checks all forward declarations for validity when considering the target type
    /// of this alias. Any inconsistencies will issue diagnostics.
    void checkForwardDecls() const;

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

    const Type* getSpecializationImpl(Compilation& compilation, LookupLocation lookupLocation,
                                      SourceLocation instanceLoc, bool forceInvalidParams,
                                      const ParameterValueAssignmentSyntax* syntax) const;

    SmallVectorSized<Definition::ParameterDecl, 8> paramDecls;

    using SpecMap = flat_hash_map<SpecializationKey, const Type*, Hasher>;
    mutable SpecMap specMap;
    mutable optional<const Type*> defaultSpecialization;
    mutable const ForwardingTypedefSymbol* firstForward = nullptr;

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

} // namespace slang
