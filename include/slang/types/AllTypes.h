//------------------------------------------------------------------------------
//! @file AllTypes.h
//! @brief All type symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/symbols/Scope.h"
#include "slang/symbols/ValueSymbol.h"
#include "slang/types/Type.h"

namespace slang {

class Compilation;
class InstanceBodySymbol;
class ModportSymbol;

struct IntegerTypeSyntax;

/// A base class for integral types, which include all scalar types, predefined integer types,
/// packed arrays, packed structures, packed unions, and enum types.
class IntegralType : public Type {
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

    static const Type& fromSyntax(Compilation& compilation, const IntegerTypeSyntax& syntax,
                                  const BindContext& context);

    static const Type& fromSyntax(Compilation& compilation, SyntaxKind integerKind,
                                  span<const VariableDimensionSyntax* const> dimensions,
                                  bool isSigned, const BindContext& context);

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind);

protected:
    IntegralType(SymbolKind kind, string_view name, SourceLocation loc, bitwidth_t bitWidth,
                 bool isSigned, bool isFourState);
};

/// Represents the single-bit scalar types.
class ScalarType : public IntegralType {
public:
    enum Kind { Bit, Logic, Reg } scalarKind;

    ScalarType(Kind scalarKind);
    ScalarType(Kind scalarKind, bool isSigned);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ScalarType; }
};

/// Represents the predefined integer types, which are essentially predefined vector types.
class PredefinedIntegerType : public IntegralType {
public:
    enum Kind { ShortInt, Int, LongInt, Byte, Integer, Time } integerKind;

    PredefinedIntegerType(Kind integerKind);
    PredefinedIntegerType(Kind integerKind, bool isSigned);

    static bool isDefaultSigned(Kind integerKind);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PredefinedIntegerType; }
};

/// Represents one of the predefined floating point types, which are used for representing real
/// numbers.
class FloatingType : public Type {
public:
    enum Kind { Real, ShortReal, RealTime } floatKind;

    explicit FloatingType(Kind floatKind);

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::FloatingType; }
};

class EnumValueSymbol;
struct EnumTypeSyntax;

/// Represents an enumerated type.
class EnumType : public IntegralType, public Scope {
public:
    const Type& baseType;
    int systemId;

    EnumType(Compilation& compilation, SourceLocation loc, const Type& baseType,
             const BindContext& context);

    static const Type& fromSyntax(Compilation& compilation, const EnumTypeSyntax& syntax,
                                  const BindContext& context, const Type* typedefTarget);
    static bool isKind(SymbolKind kind) { return kind == SymbolKind::EnumType; }

    iterator_range<specific_symbol_iterator<EnumValueSymbol>> values() const {
        return membersOfType<EnumValueSymbol>();
    }
};

/// Represents an enumerated value / member.
class EnumValueSymbol : public ValueSymbol {
public:
    EnumValueSymbol(string_view name, SourceLocation loc);

    const ConstantValue& getValue() const;
    void setValue(ConstantValue value);

    void serializeTo(ASTSerializer& serializer) const;

    static EnumValueSymbol& fromSyntax(Compilation& compilation, const DeclaratorSyntax& syntax,
                                       const Type& type, optional<int32_t> index);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::EnumValue; }

private:
    mutable const ConstantValue* value = nullptr;
};

/// Represents a packed array of some simple element type (vectors, packed structures, other packed
/// arrays).
class PackedArrayType : public IntegralType {
public:
    const Type& elementType;
    ConstantRange range;

    PackedArrayType(const Type& elementType, ConstantRange range);

    static const Type& fromSyntax(const Scope& scope, const Type& elementType, ConstantRange range,
                                  const SyntaxNode& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PackedArrayType; }
};

/// Represents a fixed size unpacked array (as opposed to a dynamically sized unpacked
/// array, associative array, or queue).
class FixedSizeUnpackedArrayType : public Type {
public:
    const Type& elementType;
    ConstantRange range;

    FixedSizeUnpackedArrayType(const Type& elementType, ConstantRange range);

    static const Type& fromDims(Compilation& compilation, const Type& elementType,
                                span<const ConstantRange> dimensions);

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::FixedSizeUnpackedArrayType; }
};

/// Represents a dynamically sized unpacked array.
class DynamicArrayType : public Type {
public:
    const Type& elementType;

    explicit DynamicArrayType(const Type& elementType);

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::DynamicArrayType; }
};

/// Represents an unpacked array that provides associative lookup.
class AssociativeArrayType : public Type {
public:
    const Type& elementType;
    const Type* indexType = nullptr;

    AssociativeArrayType(const Type& elementType, const Type* indexType);

    bool hasWildcardIndexType() const { return indexType == nullptr; }
    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::AssociativeArrayType; }
};

/// Represents an unpacked array that provides queue semantics.
class QueueType : public Type {
public:
    const Type& elementType;
    uint32_t maxBound;

    QueueType(const Type& elementType, uint32_t maxBound);

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::QueueType; }
};

struct StructUnionTypeSyntax;

/// Represents a packed structure of members.
class PackedStructType : public IntegralType, public Scope {
public:
    int systemId;

    PackedStructType(Compilation& compilation, bitwidth_t bitWidth, bool isSigned, bool isFourState,
                     SourceLocation loc, const BindContext& context);

    static const Type& fromSyntax(Compilation& compilation, const StructUnionTypeSyntax& syntax,
                                  const BindContext& context);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PackedStructType; }
};

/// Represents an unpacked structure of members.
class UnpackedStructType : public Type, public Scope {
public:
    int systemId;

    UnpackedStructType(Compilation& compilation, SourceLocation loc, const BindContext& context);

    static const Type& fromSyntax(const BindContext& context, const StructUnionTypeSyntax& syntax);

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::UnpackedStructType; }
};

/// Represents a packed union of members.
class PackedUnionType : public IntegralType, public Scope {
public:
    int systemId;
    bool isTagged;
    uint32_t tagBits;

    PackedUnionType(Compilation& compilation, bitwidth_t bitWidth, bool isSigned, bool isFourState,
                    bool isTagged, uint32_t tagBits, SourceLocation loc,
                    const BindContext& context);

    static const Type& fromSyntax(Compilation& compilation, const StructUnionTypeSyntax& syntax,
                                  const BindContext& context);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PackedUnionType; }
};

/// Represents an unpacked union of members.
class UnpackedUnionType : public Type, public Scope {
public:
    int systemId;
    bool isTagged;

    UnpackedUnionType(Compilation& compilation, bool isTagged, SourceLocation loc,
                      const BindContext& context);

    static const Type& fromSyntax(const BindContext& context, const StructUnionTypeSyntax& syntax);

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::UnpackedUnionType; }
};

/// Represents the Void (or lack of a) type. This can be used as the return type of functions
/// and as the type of members in tagged unions.
class VoidType : public Type {
public:
    VoidType() : Type(SymbolKind::VoidType, "void", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::VoidType; }
};

/// Represents the Null type. This can be used as a literal for setting class handles and
/// chandles to null (or the default value).
class NullType : public Type {
public:
    NullType() : Type(SymbolKind::NullType, "null", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::NullType; }
};

/// Represents storage for pointers passed using the DPI (a "C" compatible handle).
class CHandleType : public Type {
public:
    CHandleType() : Type(SymbolKind::CHandleType, "chandle", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CHandleType; }
};

/// Represents an ASCII string type.
class StringType : public Type {
public:
    StringType() : Type(SymbolKind::StringType, "string", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::StringType; }
};

/// Represents a SystemVerilog event handle, which is used for synchronization between
/// asynchronous processes.
class EventType : public Type {
public:
    EventType() : Type(SymbolKind::EventType, "event", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::EventType; }
};

/// Represents the '$' special token that is a standin for the unbounded end
/// of a queue or range selection.
class UnboundedType : public Type {
public:
    UnboundedType() : Type(SymbolKind::UnboundedType, "$", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::UnboundedType; }
};

/// Represents the result of a type reference expression, i.e. the type() operator.
class TypeRefType : public Type {
public:
    TypeRefType() : Type(SymbolKind::TypeRefType, "type reference", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::TypeRefType; }
};

/// Represents an 'untyped' type, which is used for e.g. arguments of sequences.
class UntypedType : public Type {
public:
    UntypedType() : Type(SymbolKind::UntypedType, "untyped", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::UntypedType; }
};

/// Represents the type of sequence instances and arguments.
class SequenceType : public Type {
public:
    SequenceType() : Type(SymbolKind::SequenceType, "sequence", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::SequenceType; }
};

/// Represents the type of property instances and arguments.
class PropertyType : public Type {
public:
    PropertyType() : Type(SymbolKind::PropertyType, "property", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PropertyType; }
};

struct VirtualInterfaceTypeSyntax;

/// Represents a virtual interface type.
class VirtualInterfaceType : public Type {
public:
    const InstanceBodySymbol& iface;
    const ModportSymbol* modport;

    VirtualInterfaceType(const InstanceBodySymbol& iface, const ModportSymbol* modport,
                         SourceLocation loc) :
        Type(SymbolKind::VirtualInterfaceType, "", loc),
        iface(iface), modport(modport) {}

    ConstantValue getDefaultValueImpl() const;

    static const Type& fromSyntax(const BindContext& context,
                                  const VirtualInterfaceTypeSyntax& syntax);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::VirtualInterfaceType; }
};

struct ClassPropertyDeclarationSyntax;
struct ForwardInterfaceClassTypedefDeclarationSyntax;
struct ForwardTypedefDeclarationSyntax;

/// A forward declaration of a user-defined type name. A given type name can have
/// an arbitrary number of forward declarations in the same scope, so each symbol
/// forms a linked list, headed by the actual type definition.
class ForwardingTypedefSymbol : public Symbol {
public:
#define CATEGORY(x) x(None) x(Enum) x(Struct) x(Union) x(Class) x(InterfaceClass)
    ENUM_MEMBER(Category, CATEGORY);
#undef CATEGORY

    Category category;
    optional<Visibility> visibility;

    ForwardingTypedefSymbol(string_view name, SourceLocation loc, Category category) :
        Symbol(SymbolKind::ForwardingTypedef, name, loc), category(category) {}

    static ForwardingTypedefSymbol& fromSyntax(const Scope& scope,
                                               const ForwardTypedefDeclarationSyntax& syntax);

    static ForwardingTypedefSymbol& fromSyntax(
        const Scope& scope, const ForwardInterfaceClassTypedefDeclarationSyntax& syntax);

    static ForwardingTypedefSymbol& fromSyntax(const Scope& scope,
                                               const ClassPropertyDeclarationSyntax& syntax);

    void addForwardDecl(const ForwardingTypedefSymbol& decl) const;
    const ForwardingTypedefSymbol* getNextForwardDecl() const { return next; }

    void checkType(Category checkCategory, Visibility checkVisibility,
                   SourceLocation declLoc) const;

    void serializeTo(ASTSerializer& serializer) const;

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ForwardingTypedef; }

private:
    mutable const ForwardingTypedefSymbol* next = nullptr;
};

struct TypedefDeclarationSyntax;

/// Represents a type alias, which is introduced via a typedef or type parameter.
class TypeAliasType : public Type {
public:
    DeclaredType targetType;
    Visibility visibility = Visibility::Public;

    TypeAliasType(string_view name, SourceLocation loc);

    static TypeAliasType& fromSyntax(const Scope& scope, const TypedefDeclarationSyntax& syntax);
    static TypeAliasType& fromSyntax(const Scope& scope,
                                     const ClassPropertyDeclarationSyntax& syntax);

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
class ErrorType : public Type {
public:
    ErrorType() : Type(SymbolKind::ErrorType, "", SourceLocation()) {}

    ConstantValue getDefaultValueImpl() const { return nullptr; }

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ErrorType; }

    static const ErrorType Instance;
};

} // namespace slang
