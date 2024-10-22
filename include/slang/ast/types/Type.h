//------------------------------------------------------------------------------
//! @file Type.h
//! @brief Base class for all expression types
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#pragma once

#include "slang/ast/Symbol.h"
#include "slang/numeric/ConstantValue.h"
#include "slang/syntax/SyntaxNode.h"
#include "slang/util/LanguageVersion.h"

namespace slang::ast {

class Compilation;
struct LookupResult;
enum class RandMode;

/// Specifies possible traits for integral types.
enum class SLANG_EXPORT IntegralFlags : uint8_t {
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
SLANG_BITMASK(IntegralFlags, Reg)

/// @brief Base class for all data types in SystemVerilog.
///
/// Note that this can actually be an alias for some other type (such as with typedefs or
/// type parameters). Each type knows its "canonical" type, which in the case of most types
/// points to itself and for type aliases points to the fully unwrapped target type. Most
/// methods on this class that query traits drill down to the canonical type.
///
class SLANG_EXPORT Type : public Symbol {
public:
    /// The maximum size in bits of any fixed size type.
    static constexpr uint64_t MaxBitWidth = uint64_t(INT32_MAX) * 8;

    /// Gets the canonical type for this type, which involves unwrapping any type aliases.
    const Type& getCanonicalType() const {
        if (!canonical)
            resolveCanonical();
        return *canonical;
    }

    /// Gets the declared width of the numeric type in bits. Returns zero if the type is not
    /// numeric (i.e. integral or floating).
    bitwidth_t getBitWidth() const;

    /// Gets $bits of the type. Returns zero if the type does not have a statically known size.
    uint64_t getBitstreamWidth() const;

    /// Gets the "selectable" width of the type. This is the size of the object when determining
    /// whether assignments to the static portions overlap with each other. Dynamically sized
    /// types are given the size of 1 for selection purposes.
    uint64_t getSelectableWidth() const;

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

    /// Indicates whether this type has a statically fixed size range associated with it.
    /// This is true for packed arrays and fixed size unpacked arrays, as well as all
    /// integral types (their range is their bitwidth).
    bool hasFixedRange() const;

    /// Indicates whether this type is convertible to a boolean predicate for use in
    /// a conditional expression.
    bool isBooleanConvertible() const;

    /// Indicates whether this is a packed or unpacked array.
    bool isArray() const;

    /// Indicates whether this is a packed or unpacked struct.
    bool isStruct() const;

    /// Indicates whether this type can be packed into a stream of bits.
    /// If @a destination is true, this is being checked in the context of the
    /// destination side of a bitstream cast, which disallows associative arrays.
    bool isBitstreamType(bool destination = false) const;

    /// Check whether this type has a fixed bitstream size, as opposed to a dynamically
    /// sized type like a dynamic array or string.
    bool isFixedSize() const;

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

    /// Indicates whether this is any form of unpacked array type:
    /// fixed size, dynamic, associative, or a queue.
    bool isUnpackedArray() const;

    /// Indicates whether this is a dynamic array, associative array, or a queue.
    bool isDynamicallySizedArray() const;

    /// Indicates whether this is a packed or unpacked union.
    bool isUnion() const;

    /// Indicates whether this is a tagged union, packed or unpacked.
    bool isTaggedUnion() const;

    /// Indicates whether this is an unpacked structure type.
    bool isUnpackedStruct() const {
        return getCanonicalType().kind == SymbolKind::UnpackedStructType;
    }

    /// Indicates whether this is a packed union type.
    bool isPackedUnion() const { return getCanonicalType().kind == SymbolKind::PackedUnionType; }

    /// Indicates whether this is an unpacked union type.
    bool isUnpackedUnion() const {
        return getCanonicalType().kind == SymbolKind::UnpackedUnionType;
    }

    /// Indicates whether this is an associative array type.
    bool isAssociativeArray() const {
        return getCanonicalType().kind == SymbolKind::AssociativeArrayType;
    }

    /// Indicates whether this is a queue type.
    bool isQueue() const { return getCanonicalType().kind == SymbolKind::QueueType; }

    /// Indicates whether this is an enum type.
    bool isEnum() const { return getCanonicalType().kind == SymbolKind::EnumType; }

    /// Indicates whether this is a class type.
    bool isClass() const { return getCanonicalType().kind == SymbolKind::ClassType; }

    /// Indicates whether this is a covergroup type.
    bool isCovergroup() const { return getCanonicalType().kind == SymbolKind::CovergroupType; }

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

    /// Indicates whether this is the unbounded type.
    bool isUnbounded() const { return getCanonicalType().kind == SymbolKind::UnboundedType; }

    /// Indicates whether this is the type reference type.
    bool isTypeRefType() const { return getCanonicalType().kind == SymbolKind::TypeRefType; }

    /// Indicates whether this is the untyped type.
    bool isUntypedType() const { return getCanonicalType().kind == SymbolKind::UntypedType; }

    /// Indicates whether this is the sequence type.
    bool isSequenceType() const { return getCanonicalType().kind == SymbolKind::SequenceType; }

    /// Indicates whether this is the property type.
    bool isPropertyType() const { return getCanonicalType().kind == SymbolKind::PropertyType; }

    /// Indicates whether this is a virtual interface type.
    bool isVirtualInterface() const {
        return getCanonicalType().kind == SymbolKind::VirtualInterfaceType;
    }

    /// Indicates whether this is an array of virtual interface types.
    /// A plain virtual interface type will also return true.
    bool isVirtualInterfaceOrArray() const;

    /// Indicates whether this is a type that acts like a handle, which includes
    /// classes, events, chandles, virtual interfaces, and the null type.
    bool isHandleType() const;

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

    /// Determines whether the given type can be bit-stream cast to this one.
    bool isBitstreamCastable(const Type& rhs) const;

    /// Returns true if this is a class type that derives from the given base
    /// class type, and false otherwise.
    bool isDerivedFrom(const Type& base) const;

    /// Returns true if this is a class type that implements the given
    /// interface class type, or if this is an interface class type that
    /// extends the given interface class type. Otherwise, returns false.
    bool implements(const Type& ifaceClass) const;

    /// Gets a combination of flags for integral types; for non-integral types,
    /// this returns all zeros.
    bitmask<IntegralFlags> getIntegralFlags() const;

    /// Gets the default value for the type. An uninitialized variable of this
    /// type will have the given default value.
    ConstantValue getDefaultValue() const;

    /// Returns the fixed range of the type, if it has one. This can be determined
    /// via the hasFixedRange() method. If it does not, this returns an empty range.
    ConstantRange getFixedRange() const;

    /// Returns the element type if this is an array type; otherwise returns nullptr.
    const Type* getArrayElementType() const;

    /// Returns the index type if this is an associative array and it has a non-wildcard
    /// index type specified. Otherwise, returns nullptr.
    const Type* getAssociativeIndexType() const;

    /// Returns true if the type can represent a string-like value; this includes
    /// the string type itself as well as byte arrays and all integral types.
    bool canBeStringLike() const;

    /// Returns true if the type can be considered iterable, which includes
    /// types like arrays and strings.
    bool isIterable() const;

    /// Returns true if the type is valid for use as a random variable of
    /// the given mode.
    bool isValidForRand(RandMode mode, LanguageVersion languageVersion) const;

    /// Returns true if the type is valid for use as a DPI return value.
    bool isValidForDPIReturn() const;

    /// Returns true if the type is valid for use as a DPI argument.
    bool isValidForDPIArg() const;

    /// Returns true if the type is valid for use in sequence expressions.
    bool isValidForSequence() const;

    /// Returns true if the type is valid for use in a port.
    bool isValidForPort(const Type** foundInvalid) const;

    /// Returns true if the type is valid for use in a union.
    bool isValidForUnion(bool isTagged, const Type** foundInvalid) const;

    /// Coerces the given constant into one that is appropriate for this type.
    ConstantValue coerceValue(const ConstantValue& value) const;

    /// If this is an integral type, returns the same type converted
    /// to a signed integral type (properly descending through sub arrays).
    /// Otherwise returns `*this`.
    const Type& makeSigned(Compilation& compilation) const;

    /// If this is an integral type, returns the same type converted
    /// to an unsigned integral type (properly descending through sub arrays).
    /// Otherwise returns `*this`.
    const Type& makeUnsigned(Compilation& compilation) const;

    /// @returns a human-friendly string representation of the type.
    std::string toString() const;

    /// @returns a hash value for the type.
    size_t hash() const;

    /// If the two given types are both class types and have a common base class somewhere
    /// in their inheritance chain, return that common type. Otherwise, returns nullptr.
    static const Type* getCommonBase(const Type& left, const Type& right);

    static const Type& fromSyntax(Compilation& compilation, const syntax::DataTypeSyntax& syntax,
                                  const ASTContext& context, const Type* typedefTarget);

    static const Type& fromSyntax(
        Compilation& compilation, const Type& elementType,
        const syntax::SyntaxList<syntax::VariableDimensionSyntax>& dimensions,
        const ASTContext& context);

    /// Constructs a type from the results of a lookup operation. Note that this will
    /// not issue any diagnostics from the result object; the caller must do that
    /// themselves if they wish.
    static const Type& fromLookupResult(Compilation& compilation, const LookupResult& result,
                                        SourceRange sourceRange, const ASTContext& context);

    static bool isKind(SymbolKind kind);

protected:
    Type(SymbolKind kind, std::string_view name, SourceLocation loc) :
        Symbol(kind, name, loc), canonical(this) {}

    static const Type& getPredefinedType(Compilation& compilation, syntax::SyntaxKind kind,
                                         bool isSigned);

    mutable const Type* canonical;

private:
    void resolveCanonical() const;

    static const Type& lookupNamedType(Compilation& compilation, const syntax::NameSyntax& syntax,
                                       const ASTContext& context, bool isTypedefTarget);
};

Diagnostic& operator<<(Diagnostic& diag, const Type& arg);

} // namespace slang::ast
