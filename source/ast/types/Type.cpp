//------------------------------------------------------------------------------
// Type.cpp
// Base class for all expression types
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/types/Type.h"

#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Bitstream.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/types/TypePrinter.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

namespace {

struct GetDefaultVisitor {
    template<typename T>
    ConstantValue visit([[maybe_unused]] const T& type) {
        if constexpr (requires { type.getDefaultValueImpl(); }) {
            return type.getDefaultValueImpl();
        }
        else {
            SLANG_UNREACHABLE;
        }
    }
};

bool isSameEnum(const EnumType& le, const EnumType& re) {
    auto ls = le.getParentScope();
    auto rs = re.getParentScope();
    if (!ls || !rs)
        return false;

    if (ls->asSymbol().kind != SymbolKind::CompilationUnit)
        return false;

    if (rs->asSymbol().kind != SymbolKind::CompilationUnit)
        return false;

    if (!le.baseType.isMatching(re.baseType))
        return false;

    auto rr = re.values();
    auto rit = rr.begin();
    for (auto& value : le.values()) {
        if (rit == rr.end())
            return false;

        if (value.name != rit->name)
            return false;

        auto& lv = value.getValue();
        auto& rv = rit->getValue();
        if (lv.bad() || rv.bad())
            return false;

        if (lv.integer() != rv.integer())
            return false;

        rit++;
    }

    return rit == rr.end();
}

} // namespace

bitwidth_t Type::getBitWidth() const {
    const Type& ct = getCanonicalType();
    if (ct.isIntegral())
        return ct.as<IntegralType>().bitWidth;

    if (ct.isFloating()) {
        switch (ct.as<FloatingType>().floatKind) {
            case FloatingType::Real:
                return 64;
            case FloatingType::RealTime:
                return 64;
            case FloatingType::ShortReal:
                return 32;
            default:
                SLANG_UNREACHABLE;
        }
    }
    return 0;
}

uint64_t Type::getBitstreamWidth() const {
    auto& ct = getCanonicalType();
    switch (ct.kind) {
        case SymbolKind::FixedSizeUnpackedArrayType:
            return ct.as<FixedSizeUnpackedArrayType>().bitstreamWidth;
        case SymbolKind::UnpackedStructType:
            return ct.as<UnpackedStructType>().bitstreamWidth;
        case SymbolKind::UnpackedUnionType:
            return ct.as<UnpackedUnionType>().bitstreamWidth;
        case SymbolKind::ClassType:
            return ct.as<ClassType>().getBitstreamWidth();
        default:
            return ct.getBitWidth();
    }
}

uint64_t Type::getSelectableWidth() const {
    auto& ct = getCanonicalType();
    switch (ct.kind) {
        case SymbolKind::FixedSizeUnpackedArrayType:
            return ct.as<FixedSizeUnpackedArrayType>().selectableWidth;
        case SymbolKind::UnpackedStructType:
            return ct.as<UnpackedStructType>().selectableWidth;
        case SymbolKind::UnpackedUnionType:
            return ct.as<UnpackedUnionType>().selectableWidth;
        default:
            uint32_t width = ct.getBitWidth();
            return width > 0 ? width : 1;
    }
}

bool Type::isSigned() const {
    const Type& ct = getCanonicalType();
    return ct.isIntegral() && ct.as<IntegralType>().isSigned;
}

bool Type::isFourState() const {
    const Type& ct = getCanonicalType();
    if (ct.isIntegral())
        return ct.as<IntegralType>().isFourState;

    if (ct.isArray())
        return ct.getArrayElementType()->isFourState();

    switch (ct.kind) {
        case SymbolKind::UnpackedStructType: {
            auto& us = ct.as<UnpackedStructType>();
            for (auto field : us.fields) {
                if (field->getType().isFourState())
                    return true;
            }
            return false;
        }
        case SymbolKind::UnpackedUnionType: {
            auto& us = ct.as<UnpackedUnionType>();
            for (auto field : us.fields) {
                if (field->getType().isFourState())
                    return true;
            }
            return false;
        }
        default:
            return false;
    }
}

bool Type::isIntegral() const {
    const Type& ct = getCanonicalType();
    return IntegralType::isKind(ct.kind);
}

bool Type::isAggregate() const {
    switch (getCanonicalType().kind) {
        case SymbolKind::FixedSizeUnpackedArrayType:
        case SymbolKind::DynamicArrayType:
        case SymbolKind::AssociativeArrayType:
        case SymbolKind::QueueType:
        case SymbolKind::UnpackedStructType:
        case SymbolKind::UnpackedUnionType:
            return true;
        default:
            return false;
    }
}

bool Type::isSimpleBitVector() const {
    const Type& ct = getCanonicalType();
    if (ct.isPredefinedInteger() || ct.isScalar())
        return true;

    return ct.kind == SymbolKind::PackedArrayType &&
           ct.as<PackedArrayType>().elementType.isScalar();
}

bool Type::hasFixedRange() const {
    const Type& ct = getCanonicalType();
    return ct.isIntegral() || ct.kind == SymbolKind::FixedSizeUnpackedArrayType;
}

bool Type::isBooleanConvertible() const {
    switch (getCanonicalType().kind) {
        case SymbolKind::NullType:
        case SymbolKind::CHandleType:
        case SymbolKind::StringType:
        case SymbolKind::EventType:
        case SymbolKind::ClassType:
        case SymbolKind::CovergroupType:
        case SymbolKind::VirtualInterfaceType:
            return true;
        default:
            return isNumeric();
    }
}

bool Type::isArray() const {
    const Type& ct = getCanonicalType();
    switch (ct.kind) {
        case SymbolKind::PackedArrayType:
        case SymbolKind::FixedSizeUnpackedArrayType:
        case SymbolKind::DynamicArrayType:
        case SymbolKind::DPIOpenArrayType:
        case SymbolKind::AssociativeArrayType:
        case SymbolKind::QueueType:
            return true;
        default:
            return false;
    }
}

bool Type::isStruct() const {
    const Type& ct = getCanonicalType();
    switch (ct.kind) {
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
            return true;
        default:
            return false;
    }
}

bool Type::isBitstreamType(bool destination) const {
    auto& ct = getCanonicalType();
    if (ct.isIntegral() || ct.isString())
        return true;

    if (ct.isUnpackedArray()) {
        if (destination && ct.kind == SymbolKind::AssociativeArrayType)
            return false;
        return ct.getArrayElementType()->isBitstreamType(destination);
    }

    if (ct.isUnpackedStruct()) {
        auto& us = ct.as<UnpackedStructType>();
        for (auto field : us.fields) {
            if (!field->getType().isBitstreamType(destination))
                return false;
        }
        return true;
    }

    if (ct.isClass()) {
        if (destination)
            return false;

        auto& classType = ct.as<ClassType>();
        if (classType.isInterface || classType.hasCycles())
            return false;

        for (auto& prop : classType.membersOfType<ClassPropertySymbol>()) {
            if (!prop.getType().isBitstreamType(destination))
                return false;
        }
        return true;
    }

    return false;
}

bool Type::isFixedSize() const {
    auto& ct = getCanonicalType();
    if (ct.isIntegral() || ct.isFloating())
        return true;

    if (ct.isUnpackedArray()) {
        if (ct.kind != SymbolKind::FixedSizeUnpackedArrayType)
            return false;

        return ct.as<FixedSizeUnpackedArrayType>().elementType.isFixedSize();
    }

    if (ct.isUnpackedStruct()) {
        auto& us = ct.as<UnpackedStructType>();
        for (auto field : us.fields) {
            if (!field->getType().isFixedSize())
                return false;
        }
        return true;
    }

    if (ct.isUnpackedUnion()) {
        auto& us = ct.as<UnpackedUnionType>();
        for (auto field : us.fields) {
            if (!field->getType().isFixedSize())
                return false;
        }
        return true;
    }

    if (ct.isClass())
        return ct.as<ClassType>().getBitstreamWidth() > 0;

    return false;
}

bool Type::isSimpleType() const {
    switch (kind) {
        case SymbolKind::PredefinedIntegerType:
        case SymbolKind::ScalarType:
        case SymbolKind::FloatingType:
        case SymbolKind::TypeAlias:
        case SymbolKind::ClassType:
        case SymbolKind::StringType:
            return true;
        default:
            return false;
    }
}

bool Type::isByteArray() const {
    const Type& ct = getCanonicalType();
    if (!ct.isUnpackedArray())
        return false;

    if (ct.kind == SymbolKind::AssociativeArrayType)
        return false;

    auto& elem = ct.getArrayElementType()->getCanonicalType();
    return elem.isPredefinedInteger() &&
           elem.as<PredefinedIntegerType>().integerKind == PredefinedIntegerType::Byte;
}

bool Type::isUnpackedArray() const {
    switch (getCanonicalType().kind) {
        case SymbolKind::FixedSizeUnpackedArrayType:
        case SymbolKind::DynamicArrayType:
        case SymbolKind::AssociativeArrayType:
        case SymbolKind::QueueType:
            return true;
        default:
            return false;
    }
}

bool Type::isDynamicallySizedArray() const {
    switch (getCanonicalType().kind) {
        case SymbolKind::DynamicArrayType:
        case SymbolKind::AssociativeArrayType:
        case SymbolKind::QueueType:
            return true;
        default:
            return false;
    }
}

bool Type::isVirtualInterfaceOrArray() const {
    auto ct = &getCanonicalType();
    while (true) {
        switch (ct->kind) {
            case SymbolKind::FixedSizeUnpackedArrayType:
            case SymbolKind::DynamicArrayType:
            case SymbolKind::QueueType:
                ct = &ct->getArrayElementType()->getCanonicalType();
                break;
            default:
                return ct->isVirtualInterface();
        }
    }
}

bool Type::isHandleType() const {
    auto ct = &getCanonicalType();
    switch (ct->kind) {
        case SymbolKind::VirtualInterfaceType:
        case SymbolKind::ClassType:
        case SymbolKind::CHandleType:
        case SymbolKind::CovergroupType:
        case SymbolKind::EventType:
        case SymbolKind::NullType:
            return true;
        default:
            return false;
    }
}

bool Type::isUnion() const {
    const Type& ct = getCanonicalType();
    switch (ct.kind) {
        case SymbolKind::UnpackedUnionType:
        case SymbolKind::PackedUnionType:
            return true;
        default:
            return false;
    }
}

bool Type::isTaggedUnion() const {
    auto& ct = getCanonicalType();
    switch (ct.kind) {
        case SymbolKind::PackedUnionType:
            return ct.as<PackedUnionType>().isTagged;
        case SymbolKind::UnpackedUnionType:
            return ct.as<UnpackedUnionType>().isTagged;
        default:
            return false;
    }
}

bool Type::isMatching(const Type& rhs) const {
    // See [6.22.1] for Matching Types.
    const Type* l = &getCanonicalType();
    const Type* r = &rhs.getCanonicalType();

    // If the two types have the same address, they are literally the same type.
    // This handles all built-in types, which are allocated once and then shared,
    // and also handles simple bit vector types that share the same range, signedness,
    // and four-stateness because we uniquify them in the compilation cache.
    // This handles checks [6.22.1] (a), (b), (c), (d), (g), and (h).
    if (l == r)
        return true;

    if (l->getSyntax() && l->getSyntax() == r->getSyntax() && l->getParentScope() &&
        l->getParentScope() == r->getParentScope())
        return true;

    // Special casing for type synonyms: real/realtime
    if (l->isFloating() && r->isFloating()) {
        auto lf = l->as<FloatingType>().floatKind;
        auto rf = r->as<FloatingType>().floatKind;
        return (lf == FloatingType::Real || lf == FloatingType::RealTime) &&
               (rf == FloatingType::Real || rf == FloatingType::RealTime);
    }

    // Handle check (e) and (f): matching predefined integers and matching vector types
    // This also handles built-in scalar synonyms and multiple instances of predefined types.
    if (l->isSimpleBitVector() && r->isSimpleBitVector() &&
        (!l->isPackedArray() || !r->isPackedArray())) {
        auto& li = l->as<IntegralType>();
        auto& ri = r->as<IntegralType>();
        return li.isSigned == ri.isSigned && li.isFourState == ri.isFourState &&
               li.getBitVectorRange() == ri.getBitVectorRange();
    }

    // Handle check (f): matching array types
    if (l->isArray() && r->isArray()) {
        // Both arrays must be of the same type (fixed, packed, associative, etc) and
        // their element types must match.
        if (l->kind != r->kind || !l->getArrayElementType()->isMatching(*r->getArrayElementType()))
            return false;

        if (l->kind == SymbolKind::PackedArrayType) {
            // If packed size, ranges must match.
            if (l->as<PackedArrayType>().range != r->as<PackedArrayType>().range)
                return false;
        }
        else if (l->kind == SymbolKind::FixedSizeUnpackedArrayType) {
            // If fixed size, ranges must match.
            if (l->as<FixedSizeUnpackedArrayType>().range !=
                r->as<FixedSizeUnpackedArrayType>().range) {
                return false;
            }
        }
        else if (l->kind == SymbolKind::AssociativeArrayType) {
            // If associative, index types must match.
            auto li = l->getAssociativeIndexType();
            auto ri = r->getAssociativeIndexType();
            if (li) {
                if (!ri || !li->isMatching(*ri))
                    return false;
            }
            else if (ri) {
                return false;
            }
        }

        // Otherwise, the arrays match.
        return true;
    }

    // This is not specified in the standard but people naturally expect it to work:
    // if an enum is declared in an include file and included in multiple compilation
    // units, they will have separate instantiations but should probably still be
    // considered as matching each other.
    if (l->kind == SymbolKind::EnumType && r->kind == SymbolKind::EnumType)
        return isSameEnum(l->as<EnumType>(), r->as<EnumType>());

    if (l->isVirtualInterface() && r->isVirtualInterface()) {
        auto& lv = l->as<VirtualInterfaceType>();
        auto& rv = r->as<VirtualInterfaceType>();
        if (!lv.iface.body.hasSameType(rv.iface.body))
            return false;

        if (lv.modport)
            return rv.modport && lv.modport->name == rv.modport->name;
        else
            return !rv.modport;
    }

    return false;
}

bool Type::isEquivalent(const Type& rhs) const {
    // See [6.22.2] for Equivalent Types
    const Type* l = &getCanonicalType();
    const Type* r = &rhs.getCanonicalType();
    if (l->isMatching(*r))
        return true;

    // (c) packed integral types are equivalent if signedness, four-statedness,
    // and bitwidth are the same.
    if (l->isIntegral() && r->isIntegral() && !l->isEnum() && !r->isEnum()) {
        const auto& li = l->as<IntegralType>();
        const auto& ri = r->as<IntegralType>();
        return li.isSigned == ri.isSigned && li.isFourState == ri.isFourState &&
               li.bitWidth == ri.bitWidth;
    }

    // (d) fixed size unpacked arrays are equivalent if element types are equivalent
    // and ranges are the same width; actual bounds may differ.
    if (l->kind == SymbolKind::FixedSizeUnpackedArrayType &&
        r->kind == SymbolKind::FixedSizeUnpackedArrayType) {
        auto& la = l->as<FixedSizeUnpackedArrayType>();
        auto& ra = r->as<FixedSizeUnpackedArrayType>();
        return la.range.width() == ra.range.width() && la.elementType.isEquivalent(ra.elementType);
    }

    // (e) dynamic arrays, associative arrays, and queues are equivalent if they
    // are the same kind and have equivalent element types.
    if (l->isUnpackedArray() && l->kind == r->kind) {
        // Associative arrays additionally must have the same index type.
        if (l->kind == SymbolKind::AssociativeArrayType) {
            auto li = l->getAssociativeIndexType();
            auto ri = r->getAssociativeIndexType();
            if (li) {
                if (!ri || !li->isEquivalent(*ri))
                    return false;
            }
            else if (ri) {
                return false;
            }
        }

        return l->getArrayElementType()->isEquivalent(*r->getArrayElementType());
    }

    // The 'untyped' type is equivalent with everything.
    if (l->isUntypedType() || r->isUntypedType())
        return true;

    // Special case for DPI open arrays, which can only be declared for arguments
    // of DPI import functions. Arrays of any width can be converted to them,
    // which we will implement here even though it's not strictly "equivalent".
    if (l->kind == SymbolKind::DPIOpenArrayType || r->kind == SymbolKind::DPIOpenArrayType) {
        if (l->kind != SymbolKind::DPIOpenArrayType)
            std::swap(l, r);

        // Any integral type converts to a packed DPI open array.
        if (l->as<DPIOpenArrayType>().isPacked)
            return r->isIntegral();

        // Unpacked open arrays match fixed size unpacked arrays of any width.
        if (r->kind == SymbolKind::FixedSizeUnpackedArrayType ||
            r->kind == SymbolKind::DynamicArrayType) {
            return l->getArrayElementType()->isEquivalent(*r->getArrayElementType());
        }
    }

    return false;
}

bool Type::isAssignmentCompatible(const Type& rhs) const {
    // See [6.22.3] for Assignment Compatible
    const Type* l = &getCanonicalType();
    const Type* r = &rhs.getCanonicalType();
    if (l->isEquivalent(*r))
        return true;

    // Any integral or floating value can be implicitly converted to a packed integer
    // value or to a floating value.
    if ((l->isIntegral() && !l->isEnum()) || l->isFloating())
        return r->isIntegral() || r->isFloating() || (r->isUnbounded() && l->isSimpleBitVector());

    if (l->isUnpackedArray() && r->isUnpackedArray()) {
        // Associative arrays are only compatible with each other.
        // This will have already been ruled out by the isEquivalent check above,
        // so we if see them here then they're not compatible.
        if (l->kind == SymbolKind::AssociativeArrayType ||
            r->kind == SymbolKind::AssociativeArrayType) {
            return false;
        }

        // Fixed size unpacked arrays, dynamic arrays, and queues can be assignment
        // compatible with each other, provided element types are equivalent and,
        // if the target is fixed size, the ranges are the same width. We don't
        // need to check the fixed size condition here, since the only way it would
        // matter is if the source (rhs) is dynamically sized, which can't be checked
        // until runtime.
        if (l->kind == r->kind && l->kind == SymbolKind::FixedSizeUnpackedArrayType)
            return false; // !isEquivalent implies unequal widths or non-equivalent elements
        return l->getArrayElementType()->isEquivalent(*r->getArrayElementType());
    }

    if (l->isClass()) {
        // Null is assignment compatible to all class types.
        if (r->isNull())
            return true;

        // Derived classes can be assigned to parent classes.
        if (r->isDerivedFrom(*l))
            return true;

        // Classes can also be assigned to interface classes that they implement.
        if (r->implements(*l))
            return true;
    }

    if (l->isVirtualInterface()) {
        if (r->isNull())
            return true;

        if (!r->isVirtualInterface())
            return false;

        auto& lv = l->as<VirtualInterfaceType>();
        auto& rv = r->as<VirtualInterfaceType>();
        if (!lv.iface.body.hasSameType(rv.iface.body))
            return false;

        // A virtual interface with no modport selected may be assigned to a
        // virtual interface with a modport selected.
        if (!rv.modport)
            return true;

        return lv.modport && lv.modport->name == rv.modport->name;
    }

    // Null can be assigned to handles.
    if (l->isCHandle() || l->isEvent() || l->isCovergroup())
        return r->isNull();

    return false;
}

bool Type::isCastCompatible(const Type& rhs) const {
    // See [6.22.4] for Cast Compatible
    const Type* l = &getCanonicalType();
    const Type* r = &rhs.getCanonicalType();
    if (l->isAssignmentCompatible(*r))
        return true;

    if (l->isEnum())
        return r->isIntegral() || r->isFloating();

    if (l->isString())
        return r->isIntegral();

    if (r->isString())
        return l->isIntegral();

    return false;
}

bool Type::isBitstreamCastable(const Type& rhs) const {
    const Type* l = &getCanonicalType();
    const Type* r = &rhs.getCanonicalType();
    if (l->isBitstreamType(true) && r->isBitstreamType()) {
        if (l->isFixedSize() && r->isFixedSize())
            return l->getBitstreamWidth() == r->getBitstreamWidth();
        else
            return Bitstream::dynamicSizesMatch(*l, *r);
    }
    return false;
}

bool Type::isDerivedFrom(const Type& base) const {
    const Type* d = &getCanonicalType();
    const Type* b = &base.getCanonicalType();
    if (!b->isClass())
        return false;

    while (d && d->isClass()) {
        d = d->as<ClassType>().getBaseClass();
        if (d == b)
            return true;
    }

    // Allow error types to be convertible / derivable from anything else,
    // to prevent knock-on errors from being reported.
    if (d && d->isError())
        return true;

    return false;
}

bool Type::implements(const Type& ifaceClass) const {
    const Type* c = &getCanonicalType();
    if (!c->isClass())
        return false;

    for (auto iface : c->as<ClassType>().getImplementedInterfaces()) {
        if (iface->isMatching(ifaceClass))
            return true;
    }

    return false;
}

bitmask<IntegralFlags> Type::getIntegralFlags() const {
    bitmask<IntegralFlags> flags;
    if (!isIntegral())
        return flags;

    const IntegralType& it = getCanonicalType().as<IntegralType>();
    if (it.isSigned)
        flags |= IntegralFlags::Signed;
    if (it.isFourState)
        flags |= IntegralFlags::FourState;
    if (it.isDeclaredReg())
        flags |= IntegralFlags::Reg;

    return flags;
}

ConstantValue Type::getDefaultValue() const {
    GetDefaultVisitor visitor;
    return visit(visitor);
}

ConstantRange Type::getFixedRange() const {
    const Type& t = getCanonicalType();
    if (t.isIntegral())
        return t.as<IntegralType>().getBitVectorRange();

    if (t.kind == SymbolKind::FixedSizeUnpackedArrayType)
        return t.as<FixedSizeUnpackedArrayType>().range;

    return {};
}

const Type* Type::getArrayElementType() const {
    const Type& t = getCanonicalType();
    switch (t.kind) {
        case SymbolKind::PackedArrayType:
            return &t.as<PackedArrayType>().elementType;
        case SymbolKind::FixedSizeUnpackedArrayType:
            return &t.as<FixedSizeUnpackedArrayType>().elementType;
        case SymbolKind::DynamicArrayType:
            return &t.as<DynamicArrayType>().elementType;
        case SymbolKind::DPIOpenArrayType:
            return &t.as<DPIOpenArrayType>().elementType;
        case SymbolKind::AssociativeArrayType:
            return &t.as<AssociativeArrayType>().elementType;
        case SymbolKind::QueueType:
            return &t.as<QueueType>().elementType;
        default:
            return nullptr;
    }
}

const Type* Type::getAssociativeIndexType() const {
    const Type& t = getCanonicalType();
    if (t.kind == SymbolKind::AssociativeArrayType)
        return t.as<AssociativeArrayType>().indexType;
    return nullptr;
}

bool Type::canBeStringLike() const {
    const Type& t = getCanonicalType();
    return t.isIntegral() || t.isString() || t.isByteArray();
}

bool Type::isIterable() const {
    const Type& t = getCanonicalType();
    return (t.hasFixedRange() || t.isArray() || t.isString()) && !t.isScalar();
}

bool Type::isValidForRand(RandMode mode, LanguageVersion languageVersion) const {
    if ((isIntegral() || isNull()) && !isTaggedUnion())
        return true;

    if (isFloating())
        return mode == RandMode::Rand && languageVersion >= LanguageVersion::v1800_2023;

    if (isArray())
        return getArrayElementType()->isValidForRand(mode, languageVersion);

    if (isClass() || isUnpackedStruct())
        return mode == RandMode::Rand;

    return false;
}

bool Type::isValidForDPIReturn() const {
    switch (getCanonicalType().kind) {
        case SymbolKind::VoidType:
        case SymbolKind::FloatingType:
        case SymbolKind::CHandleType:
        case SymbolKind::StringType:
        case SymbolKind::ScalarType:
        case SymbolKind::PredefinedIntegerType:
            return true;
        default:
            return false;
    }
}

bool Type::isValidForDPIArg() const {
    auto& ct = getCanonicalType();
    if (ct.isIntegral() || ct.isFloating() || ct.isString() || ct.isCHandle() || ct.isVoid())
        return true;

    if (ct.kind == SymbolKind::FixedSizeUnpackedArrayType ||
        ct.kind == SymbolKind::DPIOpenArrayType) {
        return ct.getArrayElementType()->isValidForDPIArg();
    }

    if (ct.isUnpackedStruct()) {
        for (auto field : ct.as<UnpackedStructType>().fields) {
            if (!field->getType().isValidForDPIArg())
                return false;
        }
        return true;
    }

    return false;
}

bool Type::isValidForSequence() const {
    // Type must be cast compatible with an integral type to be valid.
    auto& ct = getCanonicalType();
    return ct.isIntegral() || ct.isString() || ct.isFloating();
}

bool Type::isValidForPort(const Type** foundInvalid) const {
    auto& ct = getCanonicalType();
    if (ct.isUnpackedArray())
        return ct.getArrayElementType()->isValidForPort(foundInvalid);

    if (ct.isUnpackedStruct()) {
        for (auto field : ct.as<UnpackedStructType>().fields) {
            if (!field->getType().isValidForPort(foundInvalid))
                return false;
        }
    }

    if (ct.isCHandle() || ct.isVirtualInterface()) {
        *foundInvalid = &ct;
        return false;
    }

    return true;
}

bool Type::isValidForUnion(bool isTagged, const Type** foundInvalid) const {
    auto& ct = getCanonicalType();
    if (ct.isVirtualInterface() ||
        (!isTagged && (ct.isCHandle() || ct.isDynamicallySizedArray()))) {
        *foundInvalid = &ct;
        return false;
    }

    if (ct.isUnpackedArray())
        return ct.getArrayElementType()->isValidForUnion(isTagged, foundInvalid);

    if (ct.isUnpackedStruct()) {
        for (auto field : ct.as<UnpackedStructType>().fields) {
            if (!field->getType().isValidForUnion(isTagged, foundInvalid))
                return false;
        }
    }

    return true;
}

ConstantValue Type::coerceValue(const ConstantValue& value) const {
    if (isIntegral())
        return value.convertToInt(getBitWidth(), isSigned(), isFourState());

    if (isFloating()) {
        if (getBitWidth() == 32)
            return value.convertToShortReal();
        else
            return value.convertToReal();
    }

    if (isString())
        return value.convertToStr();

    return nullptr;
}

static const Type* changeSign(Compilation& compilation, const Type& type, bool set) {
    // This deliberately does not look at the canonical type; type aliases
    // are not convertible to a different signedness.
    SmallVector<ConstantRange, 4> dims;
    const Type* curr = &type;
    while (curr->kind == SymbolKind::PackedArrayType) {
        dims.push_back(curr->getFixedRange());
        curr = curr->getArrayElementType();
    }

    if (curr->kind != SymbolKind::ScalarType)
        return &type;

    auto flags = curr->getIntegralFlags();
    if (set)
        flags |= IntegralFlags::Signed;
    else
        flags &= ~IntegralFlags::Signed;

    if (dims.size() == 1)
        return &compilation.getType(type.getBitWidth(), flags);

    // Rebuild the array with the new element type.
    curr = &compilation.getScalarType(flags);
    size_t count = dims.size();
    for (size_t i = 0; i < count; i++) {
        // There's no worry about size overflow here because we started with a valid type.
        ConstantRange dim = dims[count - i - 1];
        curr = compilation.emplace<PackedArrayType>(*curr, dim, curr->getBitWidth() * dim.width());
    }

    return curr;
}

const Type& Type::makeSigned(Compilation& compilation) const {
    return *changeSign(compilation, *this, true);
}

const Type& Type::makeUnsigned(Compilation& compilation) const {
    return *changeSign(compilation, *this, false);
}

std::string Type::toString() const {
    TypePrinter printer;
    printer.options.skipTypeDefs = true;
    printer.append(*this);
    return printer.toString();
}

size_t Type::hash() const {
    size_t h = size_t(kind);
    auto& ct = getCanonicalType();
    if (ct.isScalar()) {
        auto sk = ct.as<ScalarType>().scalarKind;
        if (sk == ScalarType::Reg)
            sk = ScalarType::Logic;
        hash_combine(h, sk);
    }
    else if (ct.isFloating()) {
        auto fk = ct.as<FloatingType>().floatKind;
        if (fk == FloatingType::RealTime)
            fk = FloatingType::Real;
        hash_combine(h, fk);
    }
    else if (ct.isIntegral()) {
        auto& it = ct.as<IntegralType>();
        hash_combine(h, it.isSigned, it.isFourState, it.bitWidth);
    }
    else if (ct.kind == SymbolKind::FixedSizeUnpackedArrayType) {
        auto& uat = ct.as<FixedSizeUnpackedArrayType>();
        hash_combine(h, uat.range.left, uat.range.right, uat.elementType.hash());
    }
    else if (ct.kind == SymbolKind::DynamicArrayType) {
        auto& dat = ct.as<DynamicArrayType>();
        hash_combine(h, dat.elementType.hash());
    }
    else if (ct.kind == SymbolKind::DPIOpenArrayType) {
        auto& dat = ct.as<DPIOpenArrayType>();
        hash_combine(h, dat.isPacked, dat.elementType.hash());
    }
    else if (ct.kind == SymbolKind::AssociativeArrayType) {
        auto& aat = ct.as<AssociativeArrayType>();
        hash_combine(h, aat.elementType.hash());
        if (aat.indexType)
            hash_combine(h, aat.indexType->hash());
    }
    else if (ct.kind == SymbolKind::QueueType) {
        auto& qt = ct.as<QueueType>();
        hash_combine(h, qt.elementType.hash(), qt.maxBound);
    }
    else if (ct.kind == SymbolKind::VirtualInterfaceType) {
        auto& vi = ct.as<VirtualInterfaceType>();
        hash_combine(h, &vi.iface);
        hash_combine(h, vi.modport);
    }
    else {
        h = (size_t)slang::hash<const Type*>()(&ct);
    }
    return h;
}

const Type* Type::getCommonBase(const Type& left, const Type& right) {
    const Type* l = &left.getCanonicalType();
    const Type* r = &right.getCanonicalType();
    if (!l->isClass() || !r->isClass())
        return nullptr;

    SmallSet<const Type*, 8> parents;
    while (true) {
        if (l == r)
            return r;

        parents.emplace(l);
        l = l->as<ClassType>().getBaseClass();
        if (!l)
            break;

        if (l->isError())
            return l;

        l = &l->getCanonicalType();
    }

    while (true) {
        if (auto it = parents.find(r); it != parents.end())
            return r;

        r = r->as<ClassType>().getBaseClass();
        if (!r)
            return nullptr;

        if (r->isError())
            return r;

        r = &r->getCanonicalType();
    }
}

const Type& Type::fromSyntax(Compilation& compilation, const DataTypeSyntax& node,
                             const ASTContext& context, const Type* typedefTarget) {
    switch (node.kind) {
        case SyntaxKind::BitType:
        case SyntaxKind::LogicType:
        case SyntaxKind::RegType:
            return IntegralType::fromSyntax(compilation, node.as<IntegerTypeSyntax>(), context);
        case SyntaxKind::ByteType:
        case SyntaxKind::ShortIntType:
        case SyntaxKind::IntType:
        case SyntaxKind::LongIntType:
        case SyntaxKind::IntegerType:
        case SyntaxKind::TimeType: {
            auto& its = node.as<IntegerTypeSyntax>();
            if (!its.dimensions.empty()) {
                // Error but don't fail out; just remove the dims and keep trucking
                auto& diag = context.addDiag(diag::PackedDimsOnPredefinedType,
                                             its.dimensions[0]->openBracket.location());
                diag << LexerFacts::getTokenKindText(its.keyword.kind);
            }

            if (!its.signing)
                return compilation.getType(node.kind);

            return getPredefinedType(compilation, node.kind,
                                     its.signing.kind == TokenKind::SignedKeyword);
        }
        case SyntaxKind::RealType:
        case SyntaxKind::RealTimeType:
        case SyntaxKind::ShortRealType:
        case SyntaxKind::StringType:
        case SyntaxKind::CHandleType:
        case SyntaxKind::EventType:
        case SyntaxKind::VoidType:
        case SyntaxKind::Untyped:
        case SyntaxKind::PropertyType:
        case SyntaxKind::SequenceType:
            return compilation.getType(node.kind);
        case SyntaxKind::EnumType:
            return EnumType::findDefinition(compilation, node.as<EnumTypeSyntax>(), context);
        case SyntaxKind::StructType: {
            const auto& structUnion = node.as<StructUnionTypeSyntax>();
            return structUnion.packed
                       ? PackedStructType::fromSyntax(compilation, structUnion, context)
                       : UnpackedStructType::fromSyntax(context, structUnion);
        }
        case SyntaxKind::UnionType: {
            const auto& structUnion = node.as<StructUnionTypeSyntax>();
            return (structUnion.packed || structUnion.taggedOrSoft.kind == TokenKind::SoftKeyword)
                       ? PackedUnionType::fromSyntax(compilation, structUnion, context)
                       : UnpackedUnionType::fromSyntax(context, structUnion);
        }
        case SyntaxKind::NamedType:
            return lookupNamedType(compilation, *node.as<NamedTypeSyntax>().name, context,
                                   typedefTarget != nullptr);
        case SyntaxKind::ImplicitType: {
            auto& implicit = node.as<ImplicitTypeSyntax>();
            return IntegralType::fromSyntax(compilation, SyntaxKind::LogicType, implicit.dimensions,
                                            implicit.signing.kind == TokenKind::SignedKeyword,
                                            context);
        }
        case SyntaxKind::TypeReference: {
            auto& exprSyntax = *node.as<TypeReferenceSyntax>().expr;
            auto& expr = Expression::bind(exprSyntax, context,
                                          ASTFlags::AllowDataType | ASTFlags::TypeOperator);

            if (!expr.bad()) {
                if (expr.hasHierarchicalReference() &&
                    !compilation.hasFlag(CompilationFlags::AllowHierarchicalConst)) {
                    context.addDiag(diag::TypeRefHierarchical, exprSyntax.sourceRange());
                }

                if (expr.type->isVoid())
                    context.addDiag(diag::TypeRefVoid, exprSyntax.sourceRange());
            }

            return *expr.type;
        }
        case SyntaxKind::VirtualInterfaceType:
            return VirtualInterfaceType::fromSyntax(context, node.as<VirtualInterfaceTypeSyntax>());
        default:
            SLANG_UNREACHABLE;
    }
}

const Type& Type::fromSyntax(Compilation& compilation, const Type& elementType,
                             const SyntaxList<VariableDimensionSyntax>& dimensions,
                             const ASTContext& context) {
    if (dimensions.empty())
        return elementType;

    switch (elementType.getCanonicalType().kind) {
        case SymbolKind::SequenceType:
        case SymbolKind::PropertyType:
        case SymbolKind::UntypedType:
            if (!context.flags.has(ASTFlags::AllowInterconnect)) {
                context.addDiag(diag::InvalidArrayElemType, dimensions.sourceRange())
                    << elementType;
                return compilation.getErrorType();
            }
            break;
        default:
            break;
    }

    const Type* result = &elementType;
    size_t count = dimensions.size();
    for (size_t i = 0; i < count; i++) {
        if (result->isError())
            return *result;

        auto& syntax = *dimensions[count - i - 1];
        auto dim = context.evalDimension(syntax, /* requireRange */ false, /* isPacked */ false);

        switch (dim.kind) {
            case DimensionKind::Unknown:
                return compilation.getErrorType();
            case DimensionKind::Range:
            case DimensionKind::AbbreviatedRange:
                result = &FixedSizeUnpackedArrayType::fromDim(*context.scope, *result, dim.range,
                                                              syntax);
                break;
            case DimensionKind::Dynamic: {
                auto next = compilation.emplace<DynamicArrayType>(*result);
                next->setSyntax(syntax);
                result = next;
                break;
            }
            case DimensionKind::DPIOpenArray: {
                auto next = compilation.emplace<DPIOpenArrayType>(*result, /* isPacked */ false);
                next->setSyntax(syntax);
                result = next;
                break;
            }
            case DimensionKind::Associative: {
                auto next = compilation.emplace<AssociativeArrayType>(*result, dim.associativeType);
                next->setSyntax(syntax);
                result = next;
                break;
            }
            case DimensionKind::Queue: {
                auto next = compilation.emplace<QueueType>(*result, dim.queueMaxSize);
                next->setSyntax(syntax);
                result = next;
                break;
            }
        }
    }

    return *result;
}

bool Type::isKind(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::PredefinedIntegerType:
        case SymbolKind::ScalarType:
        case SymbolKind::FloatingType:
        case SymbolKind::EnumType:
        case SymbolKind::PackedArrayType:
        case SymbolKind::FixedSizeUnpackedArrayType:
        case SymbolKind::DynamicArrayType:
        case SymbolKind::DPIOpenArrayType:
        case SymbolKind::AssociativeArrayType:
        case SymbolKind::QueueType:
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
        case SymbolKind::PackedUnionType:
        case SymbolKind::UnpackedUnionType:
        case SymbolKind::ClassType:
        case SymbolKind::CovergroupType:
        case SymbolKind::VoidType:
        case SymbolKind::NullType:
        case SymbolKind::CHandleType:
        case SymbolKind::StringType:
        case SymbolKind::EventType:
        case SymbolKind::UnboundedType:
        case SymbolKind::TypeRefType:
        case SymbolKind::UntypedType:
        case SymbolKind::SequenceType:
        case SymbolKind::PropertyType:
        case SymbolKind::VirtualInterfaceType:
        case SymbolKind::TypeAlias:
        case SymbolKind::ErrorType:
            return true;
        default:
            return false;
    }
}

void Type::resolveCanonical() const {
    SLANG_ASSERT(kind == SymbolKind::TypeAlias);
    canonical = this;
    do {
        canonical = &canonical->as<TypeAliasType>().targetType.getType();
    } while (canonical->isAlias());
}

const Type& Type::lookupNamedType(Compilation& compilation, const NameSyntax& syntax,
                                  const ASTContext& context, bool isTypedefTarget) {
    bitmask<LookupFlags> flags = LookupFlags::Type;
    if (isTypedefTarget)
        flags |= LookupFlags::AllowIncompleteForwardTypedefs;

    LookupResult result;
    Lookup::name(syntax, context, flags, result);
    result.reportDiags(context);

    return fromLookupResult(compilation, result, syntax.sourceRange(), context);
}

const Type& Type::fromLookupResult(Compilation& compilation, const LookupResult& result,
                                   SourceRange sourceRange, const ASTContext& context) {
    const Symbol* symbol = result.found;
    if (!symbol)
        return compilation.getErrorType();

    if (!symbol->isType()) {
        if (symbol->kind == SymbolKind::NetType && context.flags.has(ASTFlags::AllowNetType)) {
            result.errorIfSelectors(context);
            return symbol->as<NetType>().getDataType();
        }

        context.addDiag(diag::NotAType, sourceRange) << symbol->name;
        return compilation.getErrorType();
    }

    const Type* finalType = &symbol->as<Type>();
    size_t count = result.selectors.size();
    for (size_t i = 0; i < count; i++) {
        // It's not possible to have dotted selectors here because the Lookup
        // operation will error if we try to dot into a type, and will only
        // return selectors if the symbol is value-like, in which case we will
        // fail the isType() check above.
        auto selectSyntax = std::get<const ElementSelectSyntax*>(result.selectors[count - i - 1]);
        auto dim = context.evalPackedDimension(*selectSyntax);
        finalType = &PackedArrayType::fromSyntax(*context.scope, *finalType, dim, *selectSyntax);
    }

    return *finalType;
}

const Type& Type::getPredefinedType(Compilation& compilation, SyntaxKind kind, bool isSigned) {
    auto& predef = compilation.getType(kind).as<IntegralType>();
    if (isSigned == predef.isSigned)
        return predef;

    if (predef.kind == SymbolKind::ScalarType)
        return *compilation.emplace<ScalarType>(predef.as<ScalarType>().scalarKind, isSigned);

    return *compilation.emplace<PredefinedIntegerType>(
        predef.as<PredefinedIntegerType>().integerKind, isSigned);
}

Diagnostic& operator<<(Diagnostic& diag, const Type& arg) {
    SLANG_ASSERT(!arg.isError());
    diag.args.emplace_back(Diagnostic::CustomArgType{SLANG_TYPEOF(const Type*), &arg});
    return diag;
}

} // namespace slang::ast
