//------------------------------------------------------------------------------
//! @file Type.h
//! @brief Base class for all expression types
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#pragma once

#include "slang/binding/ConstantValue.h"
#include "slang/symbols/Lookup.h"
#include "slang/symbols/Symbol.h"

namespace slang {

struct NameSyntax;

/// Specifies possible traits for integral types.
enum class IntegralFlags : uint8_t {
    /// The type is unsigned. This is the default.
    Unsigned = 0,

    /// The type is two state. This is the default.
    TwoState = 0,

    /// The type is signed.
    Signed = 1,

    /// The type is four state.
    FourState = 2,

    /// The type used the 'reg' keyword instead of 'logic'; they are
    /// semantically identical but preserve the distinction to allow
    /// more useful messaging.
    Reg = 4
};
BITMASK(IntegralFlags, Reg);

/// Base class for all data types in SystemVerilog.
///
/// Note that this can actually be an alias for some other type (such as with typedefs or
/// type parameters). Each type knows its "canonical" type, which in the case of most types
/// points to itself and for type aliases points to the fully unwrapped target type. Most
/// methods on this class that query traits drill down to the canonical type.
///
class Type : public Symbol {
public:
    /// Gets the canonical type for this type, which involves unwrapping any type aliases.
    const Type& getCanonicalType() const {
        if (!canonical)
            resolveCanonical();
        return *canonical;
    }

    /// Gets the total width of the type in bits. Returns zero if the type does not have a
    /// statically known size.
    bitwidth_t getBitWidth() const;

    /// Indicates whether the type can represent negative numeric values. For non-numeric types,
    /// this always returns false.
    bool isSigned() const;

    /// Indicates whether the type can represent unknown and high impedance numeric values.
    /// For aggregate types, this drills down into submembers to determine whether they are
    /// all two state or if some are four state. For all other types, this always returns false.
    bool isFourState() const;

    /// Indicates whether this is an aggregate type, which includes all unpacked structs, unions,
    /// and arrays.
    bool isAggregate() const;

    /// Indicates whether this is a singular type, which is the opposite of an aggregate type (that
    /// is, all types except unpacked structs, unions, and arrays).
    bool isSingular() const { return !isAggregate(); }

    /// Indicates whether this is an integral type, which includes all scalar types, predefined
    /// integer types, packed arrays, packed structures, packed unions, and enum types.
    bool isIntegral() const;

    /// Indicates whether this is a scalar integral type (bit, logic, or reg).
    bool isScalar() const { return getCanonicalType().kind == SymbolKind::ScalarType; }

    /// Indicates whether this is a predefined integer type.
    bool isPredefinedInteger() const {
        return getCanonicalType().kind == SymbolKind::PredefinedIntegerType;
    }

    /// Indicates whether this is a simple bit vector type, which encompasses all predefined integer
    /// types as well as scalar and vector types.
    bool isSimpleBitVector() const;

    /// Indicates whether this type is convertible to a boolean predicate for use in
    /// a conditional expression.
    bool isBooleanConvertible() const;

    /// Indicates whether this is a packed or unpacked array.
    bool isArray() const;

    /// Indicates whether this is a packed or unpacked struct.
    bool isStruct() const;

    /// Indicates whether this type can be packed into a stream of bits.
    bool isBitstreamType() const;

    /// Indicates whether this type is considered a "simple type", which includes
    /// built-in integers, reals, and alias types.
    bool isSimpleType() const;

    /// Indicates whether this type is an unpacked array of bytes. Various string-related
    /// methods in the language check for this to interpret such arguments as strings.
    bool isByteArray() const;

    /// Indicates whether this is a numeric type, which includes all integral and floating types.
    bool isNumeric() const { return isIntegral() || isFloating(); }

    /// Indicates whether this is a packed array type.
    bool isPackedArray() const { return getCanonicalType().kind == SymbolKind::PackedArrayType; }

    /// Indicates whether this is an unpacked array type.
    bool isUnpackedArray() const {
        return getCanonicalType().kind == SymbolKind::UnpackedArrayType;
    }

    /// Indicates whether this is an unpacked structure type.
    bool isUnpackedStruct() const {
        return getCanonicalType().kind == SymbolKind::UnpackedStructType;
    }

    /// Indicates whether this is an unpacked union type.
    bool isUnpackedUnion() const {
        return getCanonicalType().kind == SymbolKind::UnpackedUnionType;
    }

    /// Indicates whether this is an enum type.
    bool isEnum() const { return getCanonicalType().kind == SymbolKind::EnumType; }

    /// Indicates whether this is a class type.
    bool isClass() const { return getCanonicalType().kind == SymbolKind::ClassType; }

    /// Indicates whether this is a floating point type.
    bool isFloating() const { return getCanonicalType().kind == SymbolKind::FloatingType; }

    /// Indicates whether this is the Void type.
    bool isVoid() const { return getCanonicalType().kind == SymbolKind::VoidType; }

    /// Indicates whether this is the null type.
    bool isNull() const { return getCanonicalType().kind == SymbolKind::NullType; }

    /// Indicates whether this is a C-handle type.
    bool isCHandle() const { return getCanonicalType().kind == SymbolKind::CHandleType; }

    /// Indicates whether this is a string type.
    bool isString() const { return getCanonicalType().kind == SymbolKind::StringType; }

    /// Indicates whether this is an event type.
    bool isEvent() const { return getCanonicalType().kind == SymbolKind::EventType; }

    /// Indicates whether this is a type alias.
    /// Note that unlike other methods, this one does not unwrap to the canonical type.
    bool isAlias() const { return kind == SymbolKind::TypeAlias; }

    /// Indicates whether this is the error type.
    bool isError() const { return getCanonicalType().kind == SymbolKind::ErrorType; }

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

    /// Gets a combination of flags for integral types; for non-integral types,
    /// this returns all zeros.
    bitmask<IntegralFlags> getIntegralFlags() const;

    /// Gets the default value for the type. An uninitialized variable of this
    /// type will have the given default value.
    ConstantValue getDefaultValue() const;

    /// Returns the bounds of the array, if this is an array type.
    /// Otherwise returns an empty range.
    ConstantRange getArrayRange() const;

    /// Returns true if the type can represent a string-like value; this includes
    /// the string type itself as well as byte arrays and all integral types.
    bool canBeStringLike() const;

    std::string toString() const;

    static const Type& fromSyntax(Compilation& compilation, const DataTypeSyntax& syntax,
                                  LookupLocation location, const Scope& scope, bool forceSigned);

    /// Constructs a type from the results of a lookup operation. Note that this will
    /// not issue any diagnostics from the result object; the caller must do that
    /// themselves if they wish.
    static const Type& fromLookupResult(Compilation& compilation, const LookupResult& result,
                                        const NameSyntax& syntax, LookupLocation location,
                                        const Scope& parent);

    static bool isKind(SymbolKind kind);

protected:
    Type(SymbolKind kind, string_view name, SourceLocation loc) :
        Symbol(kind, name, loc), canonical(this) {}

    static const Type& getPredefinedType(Compilation& compilation, SyntaxKind kind, bool isSigned);

    mutable const Type* canonical;

private:
    void resolveCanonical() const;

    static const Type& lookupNamedType(Compilation& compilation, const NameSyntax& syntax,
                                       LookupLocation location, const Scope& parent);
};

} // namespace slang