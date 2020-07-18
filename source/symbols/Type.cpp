//------------------------------------------------------------------------------
// Type.cpp
// Base class for all expression types
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/Type.h"

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/parsing/LexerFacts.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/symbols/AllTypes.h"
#include "slang/symbols/TypePrinter.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

namespace {

struct GetDefaultVisitor {
    template<typename T>
    using getDefault_t = decltype(std::declval<T>().getDefaultValueImpl());

    template<typename T>
    ConstantValue visit([[maybe_unused]] const T& type) {
        if constexpr (is_detected_v<getDefault_t, T>) {
            return type.getDefaultValueImpl();
        }
        else {
            THROW_UNREACHABLE;
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
                THROW_UNREACHABLE;
        }
    }
    return 0;
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
            for (auto& field : us.membersOfType<FieldSymbol>()) {
                if (field.getType().isFourState())
                    return true;
            }
            return false;
        }
        case SymbolKind::UnpackedUnionType: {
            auto& us = ct.as<UnpackedUnionType>();
            for (auto& field : us.membersOfType<FieldSymbol>()) {
                if (field.getType().isFourState())
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

bool Type::isBitstreamType() const {
    // TODO: classes
    return isIntegral() || isUnpackedArray() || isUnpackedStruct();
}

bool Type::isSimpleType() const {
    switch (kind) {
        case SymbolKind::PredefinedIntegerType:
        case SymbolKind::ScalarType:
        case SymbolKind::FloatingType:
        case SymbolKind::TypeAlias:
            return true;
        default:
            return false;
    }
}

bool Type::isByteArray() const {
    const Type& ct = getCanonicalType();
    if (!ct.isUnpackedArray())
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

bool Type::isMatching(const Type& rhs) const {
    // See [6.22.1] for Matching Types.
    const Type* l = &getCanonicalType();
    const Type* r = &rhs.getCanonicalType();

    // If the two types have the same address, they are literally the same type.
    // This handles all built-in types, which are allocated once and then shared,
    // and also handles simple bit vector types that share the same range, signedness,
    // and four-stateness because we uniquify them in the compilation cache.
    // This handles checks [6.22.1] (a), (b), (c), (d), (g), and (h).
    if (l == r || (l->getSyntax() && l->getSyntax() == r->getSyntax()))
        return true;

    // Special casing for type synonyms: logic/reg
    if (l->isScalar() && r->isScalar()) {
        auto ls = l->as<ScalarType>().scalarKind;
        auto rs = r->as<ScalarType>().scalarKind;
        return (ls == ScalarType::Logic || ls == ScalarType::Reg) &&
               (rs == ScalarType::Logic || rs == ScalarType::Reg);
    }

    // Special casing for type synonyms: real/realtime
    if (l->isFloating() && r->isFloating()) {
        auto lf = l->as<FloatingType>().floatKind;
        auto rf = r->as<FloatingType>().floatKind;
        return (lf == FloatingType::Real || lf == FloatingType::RealTime) &&
               (rf == FloatingType::Real || rf == FloatingType::RealTime);
    }

    // Handle check (e) and (f): matching predefined integers and matching vector types
    if (l->isSimpleBitVector() && r->isSimpleBitVector() &&
        l->isPredefinedInteger() != r->isPredefinedInteger()) {
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
            auto li = l->as<AssociativeArrayType>().indexType;
            auto ri = r->as<AssociativeArrayType>().indexType;
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
            auto li = l->as<AssociativeArrayType>().indexType;
            auto ri = r->as<AssociativeArrayType>().indexType;
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
        return r->isIntegral() || r->isFloating();

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
        return l->getArrayElementType()->isEquivalent(*r->getArrayElementType());
    }

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

    // TODO: bitstream casting
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
        case SymbolKind::AssociativeArrayType:
            return &t.as<AssociativeArrayType>().elementType;
        case SymbolKind::QueueType:
            return &t.as<QueueType>().elementType;
        default:
            return nullptr;
    }
}

bool Type::canBeStringLike() const {
    const Type& t = getCanonicalType();
    return t.isIntegral() || t.isString() || t.isByteArray();
}

std::string Type::toString() const {
    TypePrinter printer;
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
    else if (ct.kind == SymbolKind::AssociativeArrayType) {
        auto& aat = ct.as<AssociativeArrayType>();
        hash_combine(h, aat.elementType.hash());
        if (aat.indexType)
            hash_combine(h, aat.indexType->hash());
    }
    else if (ct.kind == SymbolKind::QueueType) {
        auto& qt = ct.as<QueueType>();
        hash_combine(h, qt.elementType.hash(), qt.maxSize);
    }
    else {
        h = std::hash<const Type*>()(&ct);
    }
    return h;
}

const Type& Type::fromSyntax(Compilation& compilation, const DataTypeSyntax& node,
                             LookupLocation location, const Scope& parent, bool forceSigned) {
    switch (node.kind) {
        case SyntaxKind::BitType:
        case SyntaxKind::LogicType:
        case SyntaxKind::RegType:
            return IntegralType::fromSyntax(compilation, node.as<IntegerTypeSyntax>(), location,
                                            parent, forceSigned);
        case SyntaxKind::ByteType:
        case SyntaxKind::ShortIntType:
        case SyntaxKind::IntType:
        case SyntaxKind::LongIntType:
        case SyntaxKind::IntegerType:
        case SyntaxKind::TimeType: {
            auto& its = node.as<IntegerTypeSyntax>();
            if (!its.dimensions.empty()) {
                // Error but don't fail out; just remove the dims and keep trucking
                auto& diag = parent.addDiag(diag::PackedDimsOnPredefinedType,
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
            return compilation.getType(node.kind);
        case SyntaxKind::EnumType:
            return EnumType::fromSyntax(compilation, node.as<EnumTypeSyntax>(), location, parent,
                                        forceSigned);
        case SyntaxKind::StructType: {
            const auto& structUnion = node.as<StructUnionTypeSyntax>();
            return structUnion.packed
                       ? PackedStructType::fromSyntax(compilation, structUnion, location, parent,
                                                      forceSigned)
                       : UnpackedStructType::fromSyntax(parent, location, structUnion);
        }
        case SyntaxKind::UnionType: {
            const auto& structUnion = node.as<StructUnionTypeSyntax>();
            return structUnion.packed
                       ? PackedUnionType::fromSyntax(compilation, structUnion, location, parent,
                                                     forceSigned)
                       : UnpackedUnionType::fromSyntax(parent, location, structUnion);
        }
        case SyntaxKind::NamedType:
            return lookupNamedType(compilation, *node.as<NamedTypeSyntax>().name, location, parent);
        case SyntaxKind::ImplicitType: {
            auto& implicit = node.as<ImplicitTypeSyntax>();
            return IntegralType::fromSyntax(
                compilation, SyntaxKind::LogicType, implicit.dimensions,
                implicit.signing.kind == TokenKind::SignedKeyword || forceSigned, location, parent);
        }
        case SyntaxKind::TypeReference: {
            BindContext context(parent, location, BindFlags::NoHierarchicalNames);
            auto& expr = Expression::bind(*node.as<TypeReferenceSyntax>().expr, context,
                                          BindFlags::AllowDataType);
            return *expr.type;
        }
        case SyntaxKind::PropertyType:
        case SyntaxKind::SequenceType:
        case SyntaxKind::Untyped:
        case SyntaxKind::VirtualInterfaceType:
            parent.addDiag(diag::NotYetSupported, node.sourceRange());
            return compilation.getErrorType();
        default:
            THROW_UNREACHABLE;
    }
}

const Type& Type::fromSyntax(Compilation& compilation, const Type& elementType,
                             const SyntaxList<VariableDimensionSyntax>& dimensions,
                             LookupLocation location, const Scope& scope) {
    if (elementType.isError())
        return elementType;

    BindContext context(scope, location);

    const Type* result = &elementType;
    size_t count = dimensions.size();
    for (size_t i = 0; i < count; i++) {
        auto& syntax = *dimensions[count - i - 1];
        auto dim = context.evalDimension(syntax, /* requireRange */ false);

        Type* next = nullptr;
        switch (dim.kind) {
            case DimensionKind::Unknown:
                return compilation.getErrorType();
            case DimensionKind::Range:
            case DimensionKind::AbbreviatedRange:
                next = compilation.emplace<FixedSizeUnpackedArrayType>(*result, dim.range);
                break;
            case DimensionKind::Dynamic:
                next = compilation.emplace<DynamicArrayType>(*result);
                break;
            case DimensionKind::Associative:
                next = compilation.emplace<AssociativeArrayType>(*result, dim.associativeType);
                break;
            case DimensionKind::Queue:
                next = compilation.emplace<QueueType>(*result, dim.queueMaxSize);
                break;
        }

        next->setSyntax(syntax);
        result = next;
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
        case SymbolKind::AssociativeArrayType:
        case SymbolKind::QueueType:
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
        case SymbolKind::PackedUnionType:
        case SymbolKind::UnpackedUnionType:
        case SymbolKind::ClassType:
        case SymbolKind::VoidType:
        case SymbolKind::NullType:
        case SymbolKind::CHandleType:
        case SymbolKind::StringType:
        case SymbolKind::EventType:
        case SymbolKind::TypeAlias:
        case SymbolKind::ErrorType:
            return true;
        default:
            return false;
    }
}

void Type::resolveCanonical() const {
    ASSERT(kind == SymbolKind::TypeAlias);
    canonical = this;
    do {
        canonical = &canonical->as<TypeAliasType>().targetType.getType();
    } while (canonical->isAlias());
}

const Type& Type::lookupNamedType(Compilation& compilation, const NameSyntax& syntax,
                                  LookupLocation location, const Scope& parent) {
    LookupResult result;
    Lookup::name(parent, syntax, location, LookupFlags::Type, result);

    if (result.hasError())
        compilation.addDiagnostics(result.getDiagnostics());

    return fromLookupResult(compilation, result, syntax, location, parent);
}

const Type& Type::fromLookupResult(Compilation& compilation, const LookupResult& result,
                                   const NameSyntax& syntax, LookupLocation location,
                                   const Scope& parent) {
    const Symbol* symbol = result.found;
    if (!symbol)
        return compilation.getErrorType();

    if (!symbol->isType()) {
        parent.addDiag(diag::NotAType, syntax.sourceRange()) << symbol->name;
        return compilation.getErrorType();
    }

    BindContext context(parent, location);

    const Type* finalType = &symbol->as<Type>();
    size_t count = result.selectors.size();
    for (size_t i = 0; i < count; i++) {
        // TODO: handle dotted selectors
        auto selectSyntax = std::get<const ElementSelectSyntax*>(result.selectors[count - i - 1]);
        auto dim = context.evalPackedDimension(*selectSyntax);
        if (!dim)
            return compilation.getErrorType();

        finalType = &PackedArrayType::fromSyntax(compilation, *finalType, *dim, *selectSyntax);
    }

    return *finalType;
}

const Type& Type::getPredefinedType(Compilation& compilation, SyntaxKind kind, bool isSigned) {
    auto& predef = compilation.getType(kind).as<IntegralType>();
    if (isSigned == predef.isSigned)
        return predef;

    auto flags = predef.getIntegralFlags();
    if (isSigned)
        flags |= IntegralFlags::Signed;
    else
        flags &= ~IntegralFlags::Signed;

    return compilation.getType(predef.bitWidth, flags);
}

Diagnostic& operator<<(Diagnostic& diag, const Type& arg) {
    ASSERT(!arg.isError());
    diag.args.emplace_back(&arg);
    return diag;
}

NetType::NetType(NetKind netKind, string_view name, const Type& dataType) :
    Symbol(SymbolKind::NetType, name, SourceLocation()), netKind(netKind), declaredType(*this),
    isResolved(true) {

    declaredType.setType(dataType);
}

NetType::NetType(string_view name, SourceLocation location) :
    Symbol(SymbolKind::NetType, name, location), netKind(UserDefined), declaredType(*this) {
}

const NetType* NetType::getAliasTarget() const {
    if (!isResolved)
        resolve();
    return alias;
}

const NetType& NetType::getCanonical() const {
    if (auto target = getAliasTarget())
        return target->getCanonical();
    return *this;
}

const Type& NetType::getDataType() const {
    if (!isResolved)
        resolve();
    return declaredType.getType();
}

const SubroutineSymbol* NetType::getResolutionFunction() const {
    if (!isResolved)
        resolve();
    return resolver;
}

void NetType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("type", getDataType());
    if (auto target = getAliasTarget())
        serializer.write("target", *target);
}

NetType& NetType::fromSyntax(const Scope& scope, const NetTypeDeclarationSyntax& syntax) {
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<NetType>(syntax.name.valueText(), syntax.name.location());
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);

    // If this is an enum, make sure the declared type is set up before we get added to
    // any scope, so that the enum members get picked up correctly.
    if (syntax.type->kind == SyntaxKind::EnumType)
        result->declaredType.setTypeSyntax(*syntax.type);

    return *result;
}

void NetType::resolve() const {
    ASSERT(!isResolved);
    isResolved = true;

    auto syntaxNode = getSyntax();
    ASSERT(syntaxNode);

    auto scope = getParentScope();
    ASSERT(scope);

    auto& declSyntax = syntaxNode->as<NetTypeDeclarationSyntax>();
    if (declSyntax.withFunction) {
        // TODO: lookup and validate the function here
    }

    // If this is an enum, we already set the type earlier.
    if (declSyntax.type->kind == SyntaxKind::EnumType)
        return;

    // Our type syntax is either a link to another net type we are aliasing, or an actual
    // data type that we are using as the basis for a custom net type.
    if (declSyntax.type->kind == SyntaxKind::NamedType) {
        LookupResult result;
        const NameSyntax& nameSyntax = *declSyntax.type->as<NamedTypeSyntax>().name;
        Lookup::name(*scope, nameSyntax, LookupLocation::before(*this), LookupFlags::Type, result);

        if (result.found && result.found->kind == SymbolKind::NetType) {
            if (result.hasError())
                scope->getCompilation().addDiagnostics(result.getDiagnostics());

            alias = &result.found->as<NetType>();
            declaredType.copyTypeFrom(alias->getCanonical().declaredType);
            return;
        }
    }

    declaredType.setTypeSyntax(*declSyntax.type);
}

} // namespace slang