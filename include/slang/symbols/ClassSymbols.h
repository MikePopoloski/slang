//------------------------------------------------------------------------------
//! @file ClassSymbols.h
//! @brief Class-related symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>

#include "slang/compilation/Definition.h"
#include "slang/symbols/Scope.h"
#include "slang/symbols/Type.h"
#include "slang/symbols/VariableSymbols.h"

namespace slang {

struct ClassPropertyDeclarationSyntax;

class ClassPropertySymbol : public VariableSymbol {
public:
    Visibility visibility;
    uint32_t index;

    ClassPropertySymbol(string_view name, SourceLocation loc, VariableLifetime lifetime,
                        Visibility visibility, uint32_t index);

    void serializeTo(ASTSerializer& serializer) const;

    static void fromSyntax(const Scope& scope, const ClassPropertyDeclarationSyntax& syntax,
                           SmallVector<const ClassPropertySymbol*>& results);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ClassProperty; }
};

struct ClassDeclarationSyntax;

/// Represents a class definition type.
class ClassType : public Type, public Scope {
public:
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
                                      SourceLocation instanceLoc,
                                      const ParameterValueAssignmentSyntax* syntax) const;

    SmallVectorSized<Definition::ParameterDecl, 8> paramDecls;
    mutable flat_hash_map<SpecializationKey, const Type*, Hasher> specializations;
    mutable optional<const Type*> defaultSpecialization;
};

} // namespace slang
