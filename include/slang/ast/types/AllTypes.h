//------------------------------------------------------------------------------
//! @file AllTypes.h
//! @brief All type symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Scope.h"
#include "slang/ast/symbols/ValueSymbol.h"
#include "slang/ast/types/Type.h"
#include "slang/syntax/SyntaxFwd.h"
#include "slang/util/Function.h"

namespace slang::ast {

class FieldSymbol;
class InstanceSymbol;
class ModportSymbol;
struct EvaluatedDimension;

/// A base class for integral types, which include all scalar types, predefined integer types,
/// packed arrays, packed structures, packed unions, and enum types.
class SLANG_EXPORT IntegralType : public Type {
public:
    /// The total width of the type in bits.
    bitwidth_t bitWidth;

    /// Indicates whether or not the integer participates in signed arithmetic.
    bool isSigned;

    /// Indicates whether the integer is composed of 4-state bits or 2-state bits.
    bool isFourState;

    /// If this is a simple bit vector type, returns the address range of
    /// the bits in the vector. Otherwise the behavior is undefined (will assert).
    ConstantRange getBitVectorRange() const;

    /// Indicates whether the underlying type was declared using the 'reg' keyword.
    bool isDeclaredReg() const;

    static const Type& fromSyntax(Compilation& compilation, const syntax::IntegerTypeSyntax& syntax,
                                  const ASTContext& context);

    static const Type& fromSyntax(
        Compilation& compilation, syntax::SyntaxKind integerKind,
        std::span<const syntax::VariableDimensionSyntax* const> dimensions, bool isSigned,
        const ASTContext& context);

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind);

protected:
    IntegralType(SymbolKind kind, std::string_view name, SourceLocation loc, bitwidth_t bitWidth,
                 bool isSigned, bool isFourState);
};

/// Represents the single-bit scalar types.
class SLANG_EXPORT ScalarType : public IntegralType {
public:
    /// The kind of scalar type.
    enum Kind { Bit, Logic, Reg } scalarKind;

    ScalarType(Kind scalarKind);
    ScalarType(Kind scalarKind, bool isSigned);

    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ScalarType; }
};

/// Represents the predefined integer types, which are essentially predefined vector types.
class SLANG_EXPORT PredefinedIntegerType : public IntegralType {
public:
    /// The kind of predefined integer type.
    enum Kind { ShortInt, Int, LongInt, Byte, Integer, Time } integerKind;

    PredefinedIntegerType(Kind integerKind);
    PredefinedIntegerType(Kind integerKind, bool isSigned);

    void serializeTo(ASTSerializer&) const {}

    static bool isDefaultSigned(Kind integerKind);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PredefinedIntegerType; }
};

/// Represents one of the predefined floating point types,
/// which are used for representing real numbers.
class SLANG_EXPORT FloatingType : public Type {
public:
    /// The kind of floating point type.
    enum Kind { Real, ShortReal, RealTime } floatKind;

    explicit FloatingType(Kind floatKind);

    ConstantValue getDefaultValueImpl() const;
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::FloatingType; }
};

class EnumValueSymbol;

/// Represents an enumerated type.
class SLANG_EXPORT EnumType : public IntegralType, public Scope {
public:
    /// The base type of the enum.
    const Type& baseType;

    /// The system-generated ID.
    int systemId;

    EnumType(Compilation& compilation, SourceLocation loc, const Type& baseType,
             const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static const Type& fromSyntax(Compilation& compilation, const syntax::EnumTypeSyntax& syntax,
                                  const ASTContext& context,
                                  function_ref<void(const Symbol&)> insertCB);
    static const Type& findDefinition(Compilation& compilation,
                                      const syntax::EnumTypeSyntax& syntax,
                                      const ASTContext& context);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::EnumType; }

    std::ranges::subrange<specific_symbol_iterator<EnumValueSymbol>> values() const {
        return membersOfType<EnumValueSymbol>();
    }
};

/// Represents an enumerated value / member.
class SLANG_EXPORT EnumValueSymbol : public ValueSymbol {
public:
    EnumValueSymbol(std::string_view name, SourceLocation loc);

    /// Gets the value of the enum member.
    const ConstantValue& getValue(SourceRange referencingRange = {}) const;

    /// Sets the value of the enum member.
    void setValue(ConstantValue value);

    void serializeTo(ASTSerializer& serializer) const;

    static EnumValueSymbol& fromSyntax(Compilation& compilation,
                                       const syntax::DeclaratorSyntax& syntax, const Type& type,
                                       std::optional<int32_t> index);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::EnumValue; }

private:
    mutable const ConstantValue* value = nullptr;
    mutable bool evaluating = false;
};

/// Represents a packed array of some simple element type
/// (vectors, packed structures, other packed arrays).
class SLANG_EXPORT PackedArrayType : public IntegralType {
public:
    /// The underlying element type.
    const Type& elementType;

    /// The range of the array.
    ConstantRange range;

    PackedArrayType(const Type& elementType, ConstantRange range, bitwidth_t fullWidth);

    void serializeTo(ASTSerializer& serializer) const;

    static const Type& fromSyntax(const Scope& scope, const Type& elementType,
                                  const EvaluatedDimension& dimension,
                                  const syntax::SyntaxNode& syntax);

    static const Type& fromDim(const Scope& scope, const Type& elementType, ConstantRange dim,
                               syntax::DeferredSourceRange sourceRange);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PackedArrayType; }
};

/// Represents a fixed size unpacked array (as opposed to a
/// dynamically sized unpacked array, associative array, or queue).
class SLANG_EXPORT FixedSizeUnpackedArrayType : public Type {
public:
    /// The underlying element type.
    const Type& elementType;

    /// The range of the array.
    ConstantRange range;

    /// The selectable width of the array, in bits.
    uint64_t selectableWidth;

    /// The bitstream width of the array.
    uint64_t bitstreamWidth;

    FixedSizeUnpackedArrayType(const Type& elementType, ConstantRange range,
                               uint64_t selectableWidth, uint64_t bitstreamWidth);

    void serializeTo(ASTSerializer& serializer) const;

    static const Type& fromDims(const Scope& scope, const Type& elementType,
                                std::span<const ConstantRange> dimensions,
                                syntax::DeferredSourceRange sourceRange);

    static const Type& fromDim(const Scope& scope, const Type& elementType, ConstantRange dim,
                               syntax::DeferredSourceRange sourceRange);

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::FixedSizeUnpackedArrayType; }
};

/// Represents a dynamically sized unpacked array.
class SLANG_EXPORT DynamicArrayType : public Type {
public:
    /// The underlying element type.
    const Type& elementType;

    explicit DynamicArrayType(const Type& elementType);

    ConstantValue getDefaultValueImpl() const;
    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::DynamicArrayType; }
};

/// A special case for DPI imports that have "open array" typed arguments.
/// It's not otherwise possible to declare a variable with this type.
class SLANG_EXPORT DPIOpenArrayType : public Type {
public:
    /// The underlying element type.
    const Type& elementType;

    /// True if this is a packed open array, and false if it's unpacked.
    bool isPacked;

    DPIOpenArrayType(const Type& elementType, bool isPacked);

    ConstantValue getDefaultValueImpl() const;
    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::DPIOpenArrayType; }
};

/// Represents an unpacked array that provides associative lookup.
class SLANG_EXPORT AssociativeArrayType : public Type {
public:
    /// The underlying element type.
    const Type& elementType;

    /// The type used to index the associative array, or nullptr if
    /// it's a "wildcard" integral index.
    const Type* indexType = nullptr;

    AssociativeArrayType(const Type& elementType, const Type* indexType);

    /// @returns true if the array has a wildcard index type
    bool hasWildcardIndexType() const { return indexType == nullptr; }
    ConstantValue getDefaultValueImpl() const;
    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::AssociativeArrayType; }
};

/// Represents an unpacked array that provides queue semantics.
class SLANG_EXPORT QueueType : public Type {
public:
    /// The underlying element type.
    const Type& elementType;

    /// The maximum number of elements allowed in the queue.
    uint32_t maxBound;

    QueueType(const Type& elementType, uint32_t maxBound);

    ConstantValue getDefaultValueImpl() const;
    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::QueueType; }
};

/// Represents a packed structure of members.
class SLANG_EXPORT PackedStructType : public IntegralType, public Scope {
public:
    /// The system-generated ID.
    int systemId;

    PackedStructType(Compilation& compilation, bool isSigned, SourceLocation loc,
                     const ASTContext& context);

    void serializeTo(ASTSerializer&) const {}

    static const Type& fromSyntax(Compilation& compilation,
                                  const syntax::StructUnionTypeSyntax& syntax,
                                  const ASTContext& context);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PackedStructType; }
};

/// Represents an unpacked structure of members.
class SLANG_EXPORT UnpackedStructType : public Type, public Scope {
public:
    /// The fields contained in the struct.
    std::span<const FieldSymbol* const> fields;

    /// The selectable width of the struct, in bits.
    uint64_t selectableWidth = 0;

    /// The bitstream width of the struct.
    uint64_t bitstreamWidth = 0;

    /// The system-generated ID.
    int systemId;

    UnpackedStructType(Compilation& compilation, SourceLocation loc, const ASTContext& context);

    void serializeTo(ASTSerializer&) const {}

    static const Type& fromSyntax(const ASTContext& context,
                                  const syntax::StructUnionTypeSyntax& syntax);

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::UnpackedStructType; }
};

/// Represents a packed union of members.
class SLANG_EXPORT PackedUnionType : public IntegralType, public Scope {
public:
    /// The system-generated ID.
    int systemId;

    /// True if this is a tagged union.
    bool isTagged;

    /// True if this is a "soft" packed union.
    bool isSoft;

    /// The number of bits reserved for the tag, if this is
    /// a tagged union.
    uint32_t tagBits;

    PackedUnionType(Compilation& compilation, bool isSigned, bool isTagged, bool isSoft,
                    SourceLocation loc, const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static const Type& fromSyntax(Compilation& compilation,
                                  const syntax::StructUnionTypeSyntax& syntax,
                                  const ASTContext& context);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PackedUnionType; }
};

/// Represents an unpacked union of members.
class SLANG_EXPORT UnpackedUnionType : public Type, public Scope {
public:
    /// The fields contained in the union.
    std::span<const FieldSymbol* const> fields;

    /// The selectable width of the union, in bits.
    uint64_t selectableWidth = 0;

    /// The bitstream width of the union.
    uint64_t bitstreamWidth = 0;

    /// The system-generated ID.
    int systemId;

    /// True if this is a tagged union.
    bool isTagged;

    UnpackedUnionType(Compilation& compilation, bool isTagged, SourceLocation loc,
                      const ASTContext& context);

    void serializeTo(ASTSerializer& serializer) const;

    static const Type& fromSyntax(const ASTContext& context,
                                  const syntax::StructUnionTypeSyntax& syntax);

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::UnpackedUnionType; }
};

/// @brief Represents the Void (or lack of a) type.
///
/// This can be used as the return type of functions
/// and as the type of members in tagged unions.
class SLANG_EXPORT VoidType : public Type {
public:
    VoidType() : Type(SymbolKind::VoidType, "void", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::VoidType; }
};

/// @brief Represents the Null type.
///
/// This can be used as a literal for setting class handles and
/// chandles to null (or the default value).
class SLANG_EXPORT NullType : public Type {
public:
    NullType() : Type(SymbolKind::NullType, "null", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const;
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::NullType; }
};

/// Represents storage for pointers passed using the DPI (a "C" compatible handle).
class SLANG_EXPORT CHandleType : public Type {
public:
    CHandleType() : Type(SymbolKind::CHandleType, "chandle", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const;
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CHandleType; }
};

/// Represents the built-in ASCII string type.
class SLANG_EXPORT StringType : public Type {
public:
    StringType() : Type(SymbolKind::StringType, "string", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const;
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::StringType; }
};

/// Represents a SystemVerilog event handle, which is used for synchronization between
/// asynchronous processes.
class SLANG_EXPORT EventType : public Type {
public:
    EventType() : Type(SymbolKind::EventType, "event", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const;
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::EventType; }
};

/// Represents the '$' special token that is a standin for the unbounded end
/// of a queue or range selection.
class SLANG_EXPORT UnboundedType : public Type {
public:
    UnboundedType() : Type(SymbolKind::UnboundedType, "$", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::UnboundedType; }
};

/// Represents the result of a type reference expression, i.e. the type() operator.
class SLANG_EXPORT TypeRefType : public Type {
public:
    TypeRefType() : Type(SymbolKind::TypeRefType, "type reference", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::TypeRefType; }
};

/// Represents an 'untyped' type, which is used for e.g. arguments of sequences.
class SLANG_EXPORT UntypedType : public Type {
public:
    UntypedType() : Type(SymbolKind::UntypedType, "untyped", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::UntypedType; }
};

/// Represents the type of sequence instances and arguments.
class SLANG_EXPORT SequenceType : public Type {
public:
    SequenceType() : Type(SymbolKind::SequenceType, "sequence", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::SequenceType; }
};

/// Represents the type of property instances and arguments.
class SLANG_EXPORT PropertyType : public Type {
public:
    PropertyType() : Type(SymbolKind::PropertyType, "property", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PropertyType; }
};

/// Represents a virtual interface type.
class SLANG_EXPORT VirtualInterfaceType : public Type {
public:
    /// The type of interfaces that can be assigned to this virtual interface.
    const InstanceSymbol& iface;

    /// An optional modport restriction.
    const ModportSymbol* modport;

    /// True if this is a wrapper for a real interface instance, and false
    /// if it's declared as an actual virtual interface type.
    bool isRealIface;

    VirtualInterfaceType(const InstanceSymbol& iface, const ModportSymbol* modport,
                         bool isRealIface, SourceLocation loc) :
        Type(SymbolKind::VirtualInterfaceType, "", loc), iface(iface), modport(modport),
        isRealIface(isRealIface) {}

    ConstantValue getDefaultValueImpl() const;
    void serializeTo(ASTSerializer& serializer) const;

    static const Type& fromSyntax(const ASTContext& context,
                                  const syntax::VirtualInterfaceTypeSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::VirtualInterfaceType; }
};

/// @brief A forward declaration of a user-defined type name.
///
/// A given type name can have an arbitrary number of forward declarations
/// in the same scope, so each symbol forms a linked list, headed by the
/// actual type definition.
class SLANG_EXPORT ForwardingTypedefSymbol : public Symbol {
public:
    /// An optional restriction for the kind of type this can resolve to.
    ForwardTypeRestriction typeRestriction;

    /// An optional visibility modifier.
    std::optional<Visibility> visibility;

    ForwardingTypedefSymbol(std::string_view name, SourceLocation loc,
                            ForwardTypeRestriction typeRestriction) :
        Symbol(SymbolKind::ForwardingTypedef, name, loc), typeRestriction(typeRestriction) {}

    static ForwardingTypedefSymbol& fromSyntax(
        const Scope& scope, const syntax::ForwardTypedefDeclarationSyntax& syntax);

    static ForwardingTypedefSymbol& fromSyntax(
        const Scope& scope, const syntax::ClassPropertyDeclarationSyntax& syntax);

    void addForwardDecl(const ForwardingTypedefSymbol& decl) const;
    const ForwardingTypedefSymbol* getNextForwardDecl() const { return next; }

    void checkType(ForwardTypeRestriction checkRestriction, Visibility checkVisibility,
                   SourceLocation declLoc) const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ForwardingTypedef; }

private:
    mutable const ForwardingTypedefSymbol* next = nullptr;
};

/// Represents a type alias, which is introduced via a typedef or type parameter.
class SLANG_EXPORT TypeAliasType : public Type {
public:
    /// The declared type target of the alias.
    DeclaredType targetType;

    /// The visibility of the alias.
    Visibility visibility = Visibility::Public;

    TypeAliasType(std::string_view name, SourceLocation loc);

    static TypeAliasType& fromSyntax(const Scope& scope,
                                     const syntax::TypedefDeclarationSyntax& syntax);
    static TypeAliasType& fromSyntax(const Scope& scope,
                                     const syntax::ClassPropertyDeclarationSyntax& syntax);

    void addForwardDecl(const ForwardingTypedefSymbol& decl) const;
    const ForwardingTypedefSymbol* getFirstForwardDecl() const { return firstForward; }

    /// Checks all forward declarations for validity when considering the target type
    /// of this alias. Any inconsistencies will issue diagnostics.
    void checkForwardDecls() const;

    ConstantValue getDefaultValueImpl() const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::TypeAlias; }

private:
    friend class TypeParameterSymbol;

    mutable const ForwardingTypedefSymbol* firstForward = nullptr;
};

/// An empty type symbol that indicates an error occurred while trying to
/// resolve the type of some expression or declaration.
class SLANG_EXPORT ErrorType : public Type {
public:
    ErrorType() : Type(SymbolKind::ErrorType, "", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }
    void serializeTo(ASTSerializer&) const {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ErrorType; }

    static const ErrorType Instance;
};

} // namespace slang::ast
