//------------------------------------------------------------------------------
// TypeSymbols.h
// Type-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include "binding/ConstantValue.h"
#include "parsing/AllSyntax.h"
#include "symbols/Scope.h"
#include "symbols/Symbol.h"

namespace slang {

class Compilation;

/// Base class for all data types in SystemVerilog.
class Type : public Symbol {
public:
    /// Gets the canonical type for this type, which involves unwrapping any type aliases.
    const Type& getCanonicalType() const { return *canonical; }

    /// Gets the total width of the type in bits. Returns zero if the type does not have a statically known size.
    uint32_t getBitWidth() const;

    /// Indicates whether the type can represent negative numeric values. For non-numeric types, this
    /// always returns false.
    bool isSigned() const;

    /// Indicates whether the type can represent unknown and high impedance numeric values. For non-numeric
    /// types, this always returns false.
    bool isFourState() const;

    /// Indicates whether this is an aggregate type, which includes all unpacked structs, unions, and arrays.
    bool isAggregate() const;

    /// Indicates whether this is a singular type, which is the opposite of an aggregate type (that is,
    /// all types except unpacked structs, unions, and arrays).
    bool isSingular() const { return !isAggregate(); }

    /// Indicates whether this is an integral type, which includes all scalar types, predefined integer types,
    /// packed arrays, packed structures, packed unions, and enum types.
    bool isIntegral() const;

    /// Indicates whether this is a scalar integral type (bit, logic, or reg).
    bool isScalar() const { return kind == SymbolKind::ScalarType; }

    /// Indicates whether this is a predefined integer type.
    bool isPredefinedInteger() const { return kind == SymbolKind::PredefinedIntegerType; }

    /// Indicates whether this is a simple bit vector type, which encompasses all predefined integer
    /// types as well as scalar and vector types.
    bool isSimpleBitVector() const;

    /// Indicates whether this is a numeric type, which includes all integral and floating types.
    bool isNumeric() const { return isIntegral() || isFloating(); }

    /// Indicates whether this is an enum type.
    bool isEnum() const { return kind == SymbolKind::EnumType; }

    /// Indicates whether this is a class type.
    bool isClass() const { return kind == SymbolKind::ClassType; }

    /// Indicates whether this is a floating point type.
    bool isFloating() const { return kind == SymbolKind::FloatingType; }

    /// Indicates whether this is the Void type.
    bool isVoid() const { return kind == SymbolKind::VoidType; }

    /// Indicates whether this is the null type.
    bool isNull() const { return kind == SymbolKind::NullType; }

    /// Indicates whether this is a C-handle type.
    bool isCHandle() const { return kind == SymbolKind::CHandleType; }

    /// Indicates whether this is a string type.
    bool isString() const { return kind == SymbolKind::StringType; }

    /// Indicates whether this is an event type.
    bool isEvent() const { return kind == SymbolKind::EventType; }

    /// Indicates whether this is a type alias.
    bool isAlias() const { return kind == SymbolKind::TypeAlias; }

    /// Indicates whether this is the error type.
    bool isError() const { return kind == SymbolKind::ErrorType; }

    /// Determines whether the given type "matches" this one. For most intents
    /// and purposes, matching types are completely identical.
    bool isMatching(const Type& rhs) const;

    /// Determines whether the given type is "equivalent" to this one. This
    /// typically means that the two types can be implicitly converted between
    /// one another.
    bool isEquivalent(const Type& rhs) const;

    /// Determines whether the given type is "assignment compatible" to this one.
    /// This includes all equivalent types, plus types for which additional
    /// implicit conversion rules have been defined. Note that the
    /// reverse operation is not necessarily true.
    bool isAssignmentCompatible(const Type& rhs) const;

    /// Determines whether the given type is "cast compatible" to this one. This
    /// means that the type is either implicitly or explicitly convertible to
    /// this one. Note that the reverse operation is not necessarily true.
    bool isCastCompatible(const Type& rhs) const;

    std::string toString() const;

    static const Type& fromSyntax(Compilation& compilation, const DataTypeSyntax& syntax,
                                  LookupLocation location, const Scope& scope);
    static bool isKind(SymbolKind kind);

protected:
    Type(SymbolKind kind, string_view name, SourceLocation loc) :
        Symbol(kind, name, loc), canonical(this) {}

    const Type* canonical;
};

/// A base class for integral types, which include all scalar types, predefined integer types,
/// packed arrays, packed structures, packed unions, and enum types.
class IntegralType : public Type {
public:
    /// The total width of the type in bits.
    uint32_t bitWidth;

    /// Indicates whether or not the integer participates in signed arithmetic.
    bool isSigned;

    /// Indicates whether the integer is composed of 4-state bits or 2-state bits.
    bool isFourState;

    /// If this is a simple bit vector type, returns the address range of
    /// the bits in the vector. Otherwise the behavior is undefined (will assert).
    ConstantRange getBitVectorRange() const;

    static const Type& fromSyntax(Compilation& compilation, const IntegerTypeSyntax& syntax,
                                  LookupLocation location, const Scope& scope);

    static bool isKind(SymbolKind kind);

protected:
    IntegralType(SymbolKind kind, string_view name, SourceLocation loc, uint32_t bitWidth,
                 bool isSigned, bool isFourState);

    static bool evaluateConstantDims(Compilation& compilation,
                                     const SyntaxList<VariableDimensionSyntax>& dimensions,
                                     SmallVector<ConstantRange>& results,
                                     LookupLocation location, const Scope& scope);
};

/// Represents the single-bit scalar types.
class ScalarType : public IntegralType {
public:
    enum Kind {
        Bit,
        Logic,
        Reg
    } scalarKind;

    ScalarType(Kind scalarKind);
    ScalarType(Kind scalarKind, bool isSigned);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ScalarType; }
};

/// Represents the predefined integer types, which are essentially predefined vector types.
class PredefinedIntegerType : public IntegralType {
public:
    enum Kind {
        ShortInt,
        Int,
        LongInt,
        Byte,
        Integer,
        Time
    } integerKind;

    PredefinedIntegerType(Kind integerKind);
    PredefinedIntegerType(Kind integerKind, bool isSigned);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PredefinedIntegerType; }
};

/// Represents one of the predefined floating point types, which are used for representing real numbers.
class FloatingType : public Type {
public:
    enum Kind {
        Real,
        ShortReal,
        RealTime
    } floatKind;

    explicit FloatingType(Kind floatKind);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::FloatingType; }
};

class EnumValueSymbol;

/// Represents an enumerated type.
class EnumType : public IntegralType, public Scope {
public:
    const IntegralType& baseType;

    EnumType(Compilation& compilation, SourceLocation loc, const IntegralType& baseType, const Scope& scope);

    static const Type& fromSyntax(Compilation& compilation, const EnumTypeSyntax& syntax,
                                  LookupLocation location, const Scope& scope);
    static bool isKind(SymbolKind kind) { return kind == SymbolKind::EnumType; }

    iterator_range<specific_symbol_iterator<EnumValueSymbol>> values() const {
        return membersOfType<EnumValueSymbol>();
    }
};

/// Represents an enumerated value / member.
class EnumValueSymbol : public ValueSymbol {
public:
    const Type& type;
    const ConstantValue& value;

    EnumValueSymbol(Compilation& compilation, string_view name, SourceLocation loc,
                    const Type& type, ConstantValue value);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::EnumValue; }
};

/// Represents a packed array of some simple element type (vectors, packed structures, other packed arrays).
class PackedArrayType : public IntegralType {
public:
    const Type& elementType;
    ConstantRange range;

    PackedArrayType(const Type& elementType, ConstantRange range);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PackedArrayType; }
};

/// Represents a packed structure of members.
class PackedStructType : public IntegralType, public Scope {
public:
    PackedStructType(Compilation& compilation, uint32_t bitWidth, bool isSigned, bool isFourState);

    static const Type& fromSyntax(Compilation& compilation, const StructUnionTypeSyntax& syntax,
                                  LookupLocation location, const Scope& scope);

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::PackedStructType; }
};

/// Represents an unpacked structure of members.
class UnpackedStructType : public Type, public Scope {
public:
    explicit UnpackedStructType(Compilation& compilation);

    static const Type& fromSyntax(Compilation& compilation, const StructUnionTypeSyntax& syntax,
                                  LookupLocation location, const Scope& scope);
};

/// Represents the Void (or lack of a) type. This can be used as the return type of functions
/// and as the type of members in tagged unions.
class VoidType : public Type {
public:
    VoidType() : Type(SymbolKind::VoidType, "void", SourceLocation()) {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::VoidType; }
};

/// Represents the Null type. This can be used as a literal for setting class handles and
/// chandles to null (or the default value).
class NullType : public Type {
public:
    NullType() : Type(SymbolKind::NullType, "null", SourceLocation()) {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::NullType; }
};

/// Represents storage for pointers passed using the DPI (a "C" compatible handle).
class CHandleType : public Type {
public:
    CHandleType() : Type(SymbolKind::CHandleType, "chandle", SourceLocation()) {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::CHandleType; }
};

/// Represents an ASCII string type.
class StringType : public Type {
public:
    StringType() : Type(SymbolKind::StringType, "string", SourceLocation()) {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::StringType; }
};

/// Represents a SystemVerilog event handle, which is used for synchronization between
/// asynchronous processes.
class EventType : public Type {
public:
    EventType() : Type(SymbolKind::EventType, "event", SourceLocation()) {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::EventType; }
};

/// Represents a type alias, which is introduced via a typedef or type parameter.
class TypeAliasType : public Type {
};

/// An empty type symbol that indicates an error occurred while trying to
/// resolve the type of some expression or declaration.
class ErrorType : public Type {
public:
    ErrorType() : Type(SymbolKind::ErrorType, "", SourceLocation()) {}

    static bool isKind(SymbolKind kind) { return kind == SymbolKind::ErrorType; }

    static const ErrorType Instance;
};

}
