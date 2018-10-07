//------------------------------------------------------------------------------
// TypeSymbols.cpp
// Contains type-related symbol definitions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/symbols/TypeSymbols.h"

#include <nlohmann/json.hpp>

#include "slang/binding/ConstantValue.h"
#include "slang/compilation/Compilation.h"
#include "slang/symbols/TypePrinter.h"

namespace {

using namespace slang;

// clang-format off
bitwidth_t getWidth(PredefinedIntegerType::Kind kind) {
    switch (kind) {
        case PredefinedIntegerType::ShortInt: return 16;
        case PredefinedIntegerType::Int: return 32;
        case PredefinedIntegerType::LongInt: return 64;
        case PredefinedIntegerType::Byte: return 8;
        case PredefinedIntegerType::Integer: return 32;
        case PredefinedIntegerType::Time: return 64;
        default: THROW_UNREACHABLE;
    }
}

bool getSigned(PredefinedIntegerType::Kind kind) {
    switch (kind) {
        case PredefinedIntegerType::ShortInt: return true;
        case PredefinedIntegerType::Int: return true;
        case PredefinedIntegerType::LongInt: return true;
        case PredefinedIntegerType::Byte: return true;
        case PredefinedIntegerType::Integer: return true;
        case PredefinedIntegerType::Time: return false;
        default: THROW_UNREACHABLE;
    }
}

bool getFourState(PredefinedIntegerType::Kind kind) {
    switch (kind) {
        case PredefinedIntegerType::ShortInt: return false;
        case PredefinedIntegerType::Int: return false;
        case PredefinedIntegerType::LongInt: return false;
        case PredefinedIntegerType::Byte: return false;
        case PredefinedIntegerType::Integer: return true;
        case PredefinedIntegerType::Time: return true;
        default: THROW_UNREACHABLE;
    }
}
// clang-format on

struct GetDefaultVisitor {
    HAS_METHOD_TRAIT(getDefaultValueImpl);

    template<typename T>
    ConstantValue visit([[maybe_unused]] const T& type) {
        if constexpr (has_getDefaultValueImpl_v<T, ConstantValue>) {
            return type.getDefaultValueImpl();
        }
        else {
            THROW_UNREACHABLE;
        }
    }
};

} // namespace

namespace slang {

const ErrorType ErrorType::Instance;

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
    return ct.isIntegral() && ct.as<IntegralType>().isFourState;
}

bool Type::isIntegral() const {
    const Type& ct = getCanonicalType();
    return IntegralType::isKind(ct.kind);
}

bool Type::isAggregate() const {
    switch (getCanonicalType().kind) {
        case SymbolKind::UnpackedArrayType:
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

bool Type::isStructUnion() const {
    const Type& ct = getCanonicalType();
    switch (ct.kind) {
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
        case SymbolKind::PackedUnionType:
        case SymbolKind::UnpackedUnionType:
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
    if (l == r)
        return true;

    // Handle check (e) and (f): matching predefined integers and matching vector types
    if (l->isSimpleBitVector() && r->isSimpleBitVector()) {
        const auto& li = l->as<IntegralType>();
        const auto& ri = r->as<IntegralType>();
        return li.isSigned == ri.isSigned && li.isFourState && ri.isFourState &&
               li.getBitVectorRange() == ri.getBitVectorRange();
    }

    // Handle check (f): matching packed array types
    if (l->kind == SymbolKind::PackedArrayType && r->kind == SymbolKind::PackedArrayType) {
        return l->as<PackedArrayType>().elementType.isMatching(
            r->as<PackedArrayType>().elementType);
    }

    return false;
}

bool Type::isEquivalent(const Type& rhs) const {
    // See [6.22.2] for Equivalent Types
    const Type* l = &getCanonicalType();
    const Type* r = &rhs.getCanonicalType();
    if (l->isMatching(*r))
        return true;

    if (l->isIntegral() && r->isIntegral() && !l->isEnum() && !r->isEnum()) {
        const auto& li = l->as<IntegralType>();
        const auto& ri = r->as<IntegralType>();
        return li.isSigned == ri.isSigned && li.isFourState && ri.isFourState &&
               li.bitWidth == ri.bitWidth;
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

std::string Type::toString() const {
    TypePrinter printer;
    printer.append(*this);
    return printer.toString();
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
            // TODO: signing
            // TODO: report this error in the parser?
            // auto& its = syntax->as<IntegerTypeSyntax>();
            // if (its.dimensions.count() > 0) {
            //    // Error but don't fail out; just remove the dims and keep trucking
            //    auto& diag = addDiag(DiagCode::PackedDimsOnPredefinedType,
            //    its.dimensions[0]->openBracket.location()); diag <<
            //    getTokenKindText(its.keyword.kind);
            //}
            return compilation.getType(node.kind);
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
            return structUnion.packed ? PackedStructType::fromSyntax(compilation, structUnion,
                                                                     location, parent, forceSigned)
                                      : UnpackedStructType::fromSyntax(compilation, structUnion);
        }
        case SyntaxKind::NamedType:
            return lookupNamedType(compilation, *node.as<NamedTypeSyntax>().name, location, parent);
        case SyntaxKind::ImplicitType: {
            auto& implicit = node.as<ImplicitTypeSyntax>();
            return IntegralType::fromSyntax(
                compilation, SyntaxKind::LogicType, implicit.dimensions,
                implicit.signing.kind == TokenKind::SignedKeyword || forceSigned, location, parent);
        }
        default:
            THROW_UNREACHABLE;
    }
}

bool Type::isKind(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::PredefinedIntegerType:
        case SymbolKind::ScalarType:
        case SymbolKind::FloatingType:
        case SymbolKind::EnumType:
        case SymbolKind::PackedArrayType:
        case SymbolKind::UnpackedArrayType:
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
        case SymbolKind::NetType:
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
    parent.lookupName(syntax, location, LookupNameKind::Type, LookupFlags::None, result);

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
        parent.addDiag(DiagCode::NotAType, syntax.sourceRange()) << symbol->name;
        return compilation.getErrorType();
    }

    const Type* finalType = &symbol->as<Type>();
    for (const auto& selector : result.selectors) {
        // TODO: handle dotted selectors
        // TODO: empty selector syntax?
        const ElementSelectSyntax* selectSyntax = std::get<const ElementSelectSyntax*>(selector);
        auto dim = evaluateDimension(compilation, *selectSyntax->selector, location, parent);
        if (!dim)
            return compilation.getErrorType();

        finalType = compilation.emplace<PackedArrayType>(*finalType, *dim);
    }

    return *finalType;
}

optional<ConstantRange> Type::evaluateDimension(Compilation& compilation,
                                                const SelectorSyntax& syntax,
                                                LookupLocation location, const Scope& scope) {
    if (syntax.kind != SyntaxKind::SimpleRangeSelect) {
        scope.addDiag(DiagCode::PackedDimRequiresConstantRange, syntax.sourceRange());
        return std::nullopt;
    }

    const RangeSelectSyntax& range = syntax.as<RangeSelectSyntax>();
    auto left = compilation.evalIntegerExpr(*range.left, location, scope);
    auto right = compilation.evalIntegerExpr(*range.right, location, scope);
    if (!left || !right)
        return std::nullopt;

    // TODO: check should include size of underlying type
    int64_t diff = *left - *right;
    diff = (diff < 0 ? -diff : diff) + 1;
    if (diff > SVInt::MAX_BITS) {
        auto& diag = scope.addDiag(DiagCode::ValueExceedsMaxBitWidth, range.range.location());
        diag << range.left->sourceRange();
        diag << range.right->sourceRange();
        diag << (int)SVInt::MAX_BITS;
        return std::nullopt;
    }

    return ConstantRange{ *left, *right };
}

IntegralType::IntegralType(SymbolKind kind, string_view name, SourceLocation loc,
                           bitwidth_t bitWidth_, bool isSigned_, bool isFourState_) :
    Type(kind, name, loc),
    bitWidth(bitWidth_), isSigned(isSigned_), isFourState(isFourState_) {
}

bool IntegralType::isKind(SymbolKind kind) {
    switch (kind) {
        case SymbolKind::PredefinedIntegerType:
        case SymbolKind::ScalarType:
        case SymbolKind::EnumType:
        case SymbolKind::PackedArrayType:
        case SymbolKind::PackedStructType:
        case SymbolKind::PackedUnionType:
            return true;
        default:
            return false;
    }
}

ConstantRange IntegralType::getBitVectorRange() const {
    if (isPredefinedInteger() || isScalar() || kind == SymbolKind::PackedStructType ||
        kind == SymbolKind::PackedUnionType) {

        return { int32_t(bitWidth - 1), 0 };
    }

    return as<PackedArrayType>().range;
}

bool IntegralType::isDeclaredReg() const {
    const Type* type = this;
    while (type->kind == SymbolKind::PackedArrayType)
        type = &type->as<PackedArrayType>().elementType.getCanonicalType();

    if (type->isScalar())
        return type->as<ScalarType>().scalarKind == ScalarType::Reg;

    return false;
}

const Type& IntegralType::fromSyntax(Compilation& compilation, SyntaxKind integerKind,
                                     span<const VariableDimensionSyntax* const> dimensions,
                                     bool isSigned, LookupLocation location, const Scope& scope) {
    // This is a simple integral vector (possibly of just one element).
    SmallVectorSized<std::pair<ConstantRange, const SyntaxNode*>, 4> dims;
    for (auto dimSyntax : dimensions) {
        // TODO: better checking for these cases
        if (!dimSyntax->specifier ||
            dimSyntax->specifier->kind != SyntaxKind::RangeDimensionSpecifier) {
            return compilation.getErrorType();
        }

        auto selector = dimSyntax->specifier->as<RangeDimensionSpecifierSyntax>().selector;
        auto dim = evaluateDimension(compilation, *selector, location, scope);
        if (!dim)
            return compilation.getErrorType();

        dims.emplace(*dim, dimSyntax);
    }

    bitmask<IntegralFlags> flags;
    if (integerKind == SyntaxKind::RegType)
        flags |= IntegralFlags::Reg;
    if (isSigned)
        flags |= IntegralFlags::Signed;
    if (integerKind != SyntaxKind::BitType)
        flags |= IntegralFlags::FourState;

    // TODO: review this whole mess

    if (dims.empty()) {
        // TODO: signing
        return compilation.getType(integerKind);
    }
    else if (dims.size() == 1 && dims[0].first.right == 0) {
        // if we have the common case of only one dimension and lsb == 0
        // then we can use the shared representation
        int width = dims[0].first.left + 1;
        return compilation.getType(bitwidth_t(width), flags);
    }

    const IntegralType* result = &compilation.getScalarType(flags);
    for (uint32_t i = 0; i < dims.size(); i++) {
        auto packed = compilation.emplace<PackedArrayType>(*result, dims[i].first);
        packed->setSyntax(*dims[i].second);
        result = packed;
    }

    return *result;
}

const Type& IntegralType::fromSyntax(Compilation& compilation, const IntegerTypeSyntax& syntax,
                                     LookupLocation location, const Scope& scope,
                                     bool forceSigned) {
    return fromSyntax(compilation, syntax.kind, syntax.dimensions,
                      syntax.signing.kind == TokenKind::SignedKeyword || forceSigned, location,
                      scope);
}

ConstantValue IntegralType::getDefaultValueImpl() const {
    if (isEnum())
        return as<EnumType>().baseType.getDefaultValue();

    if (isFourState)
        return SVInt::createFillX(bitWidth, isSigned);
    else
        return SVInt(bitWidth, 0, isSigned);
}

PredefinedIntegerType::PredefinedIntegerType(Kind integerKind) :
    PredefinedIntegerType(integerKind, getSigned(integerKind)) {
}

PredefinedIntegerType::PredefinedIntegerType(Kind integerKind, bool isSigned) :
    IntegralType(SymbolKind::PredefinedIntegerType, "", SourceLocation(), getWidth(integerKind),
                 isSigned, getFourState(integerKind)),
    integerKind(integerKind) {
}

bool PredefinedIntegerType::isDefaultSigned(Kind integerKind) {
    return getSigned(integerKind);
}

ScalarType::ScalarType(Kind scalarKind) : ScalarType(scalarKind, false) {
}

ScalarType::ScalarType(Kind scalarKind, bool isSigned) :
    IntegralType(SymbolKind::ScalarType, "", SourceLocation(), 1, isSigned,
                 scalarKind != Kind::Bit),
    scalarKind(scalarKind) {
}

FloatingType::FloatingType(Kind floatKind_) :
    Type(SymbolKind::FloatingType, "", SourceLocation()), floatKind(floatKind_) {
}

ConstantValue FloatingType::getDefaultValueImpl() const {
    return 0.0;
}

EnumType::EnumType(Compilation& compilation, SourceLocation loc, const IntegralType& baseType_,
                   const Scope& scope) :
    IntegralType(SymbolKind::EnumType, "", loc, baseType_.getBitWidth(), baseType_.isSigned,
                 baseType_.isFourState),
    Scope(compilation, this), baseType(baseType_) {

    // Enum types don't live as members of the parent scope (they're "owned" by the declaration
    // containing them) but we hook up the parent pointer so that it can participate in name
    // lookups.
    setParent(scope);
}

const Type& EnumType::fromSyntax(Compilation& compilation, const EnumTypeSyntax& syntax,
                                 LookupLocation location, const Scope& scope, bool forceSigned) {
    const Type* base;
    if (!syntax.baseType)
        base = &compilation.getIntType();
    else {
        base = &compilation.getType(*syntax.baseType, location, scope, false, forceSigned);

        const Type& canonicalBase = base->getCanonicalType();
        if (canonicalBase.isError())
            return canonicalBase;

        if (!canonicalBase.isSimpleBitVector()) {
            scope.addDiag(DiagCode::InvalidEnumBase, syntax.baseType->getFirstToken().location())
                << *base;
            return compilation.getErrorType();
        }
    }

    const IntegralType& integralBase = base->as<IntegralType>();
    auto resultType =
        compilation.emplace<EnumType>(compilation, syntax.keyword.location(), integralBase, scope);
    resultType->setSyntax(syntax);

    SVInt one(integralBase.bitWidth, 1, integralBase.isSigned);
    SVInt current(integralBase.bitWidth, 0, integralBase.isSigned);

    for (auto member : syntax.members) {
        auto ev =
            compilation.emplace<EnumValueSymbol>(member->name.valueText(), member->name.location());
        ev->setType(*resultType);
        ev->setSyntax(*member);
        resultType->addMember(*ev);

        if (!member->initializer) {
            ev->setValue(current);
            current += one;
        }
        else {
            // TODO: require integer in binding
            ev->setInitializerSyntax(*member->initializer->expr,
                                     member->initializer->equals.location());
            if (auto& cv = ev->getConstantValue())
                current = cv.integer() + one;
            else
                current += one;
        }
    }

    return *resultType;
}

EnumValueSymbol::EnumValueSymbol(string_view name, SourceLocation loc) :
    ValueSymbol(SymbolKind::EnumValue, name, loc, DeclaredTypeFlags::RequireIntegerConstant) {
}

const ConstantValue& EnumValueSymbol::getValue() const {
    return value ? *value : getConstantValue();
}

void EnumValueSymbol::setValue(ConstantValue newValue) {
    auto scope = getScope();
    ASSERT(scope);
    value = scope->getCompilation().createConstant(std::move(newValue));
}

void EnumValueSymbol::toJson(json& j) const {
    j["type"] = getType();
    j["value"] = getValue();
}

PackedArrayType::PackedArrayType(const Type& elementType, ConstantRange range) :
    IntegralType(SymbolKind::PackedArrayType, "", SourceLocation(),
                 elementType.getBitWidth() * range.width(), elementType.isSigned(),
                 elementType.isFourState()),
    elementType(elementType), range(range) {
}

UnpackedArrayType::UnpackedArrayType(const Type& elementType, ConstantRange range) :
    Type(SymbolKind::UnpackedArrayType, "", SourceLocation()), elementType(elementType),
    range(range) {
}

const Type& UnpackedArrayType::fromSyntax(Compilation& compilation, const Type& elementType,
                                          LookupLocation location, const Scope& scope,
                                          const SyntaxList<VariableDimensionSyntax>& dimensions) {
    const Type* result = &elementType;
    uint32_t count = (uint32_t)dimensions.size();
    for (uint32_t i = 0; i < count; i++) {
        // TODO: handle other kinds of unpacked arrays
        const VariableDimensionSyntax& dim = *dimensions[count - i - 1];
        if (!dim.specifier || dim.specifier->kind != SyntaxKind::RangeDimensionSpecifier)
            return compilation.getErrorType();

        ConstantRange range;
        auto selector = dim.specifier->as<RangeDimensionSpecifierSyntax>().selector;
        switch (selector->kind) {
            case SyntaxKind::BitSelect: {
                auto left = compilation.evalIntegerExpr(*selector->as<BitSelectSyntax>().expr,
                                                        location, scope);
                if (!left)
                    return compilation.getErrorType();

                if (*left <= 0) {
                    scope.addDiag(DiagCode::ValueMustBePositive, selector->sourceRange());
                    return compilation.getErrorType();
                }

                range = { 0, *left - 1 };
                break;
            }
            case SyntaxKind::SimpleRangeSelect: {
                auto& rangeSyntax = selector->as<RangeSelectSyntax>();
                auto left = compilation.evalIntegerExpr(*rangeSyntax.left, location, scope);
                auto right = compilation.evalIntegerExpr(*rangeSyntax.right, location, scope);
                if (!left || !right)
                    return compilation.getErrorType();

                range = { *left, *right };
                break;
            }
            default: {
                scope.addDiag(DiagCode::InvalidUnpackedDimension, selector->sourceRange());
                return compilation.getErrorType();
            }
        }

        auto unpacked = compilation.emplace<UnpackedArrayType>(*result, range);
        unpacked->setSyntax(dim);
        result = unpacked;
    }

    return *result;
}

ConstantValue UnpackedArrayType::getDefaultValueImpl() const {
    // TODO: implement this
    THROW_UNREACHABLE;
}

bool FieldSymbol::isPacked() const {
    const Scope* scope = getScope();
    ASSERT(scope);
    return scope->asSymbol().kind == SymbolKind::PackedStructType ||
           scope->asSymbol().kind == SymbolKind::UnpackedStructType;
}

PackedStructType::PackedStructType(Compilation& compilation, bitwidth_t bitWidth, bool isSigned,
                                   bool isFourState) :
    IntegralType(SymbolKind::PackedStructType, "", SourceLocation(), bitWidth, isSigned,
                 isFourState),
    Scope(compilation, this) {
}

const Type& PackedStructType::fromSyntax(Compilation& compilation,
                                         const StructUnionTypeSyntax& syntax,
                                         LookupLocation location, const Scope& scope,
                                         bool forceSigned) {
    ASSERT(syntax.packed);
    bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword || forceSigned;
    bool isFourState = false;
    bitwidth_t bitWidth = 0;

    // We have to look at all the members up front to know our width and four-statedness.
    // We have to iterate in reverse because members are specified from MSB to LSB order.
    SmallVectorSized<const Symbol*, 8> members;
    for (auto member : make_reverse_range(syntax.members)) {
        const Type& type = compilation.getType(*member->type, location, scope);
        isFourState |= type.isFourState();

        bool issuedError = false;
        if (!type.isIntegral() && !type.isError()) {
            issuedError = true;
            auto& diag = scope.addDiag(DiagCode::PackedMemberNotIntegral,
                                       member->type->getFirstToken().location());
            diag << type;
            diag << member->type->sourceRange();
        }

        for (auto decl : member->declarators) {
            auto variable = compilation.emplace<FieldSymbol>(decl->name.valueText(),
                                                             decl->name.location(), bitWidth);
            variable->setType(type);
            variable->setSyntax(*decl);
            members.append(variable);

            // Unpacked arrays are disallowed in packed structs.
            if (const Type& dimType = compilation.getType(type, decl->dimensions, location, scope);
                dimType.isUnpackedArray() && !issuedError) {

                auto& diag = scope.addDiag(DiagCode::PackedMemberNotIntegral, decl->name.range());
                diag << dimType;
                diag << decl->dimensions.sourceRange();
            }

            bitWidth += type.getBitWidth();

            if (decl->initializer) {
                auto& diag = scope.addDiag(DiagCode::PackedMemberHasInitializer,
                                           decl->initializer->equals.location());
                diag << decl->initializer->expr->sourceRange();
            }
        }
    }

    auto result =
        compilation.emplace<PackedStructType>(compilation, bitWidth, isSigned, isFourState);
    for (auto member : make_reverse_range(members))
        result->addMember(*member);

    result->setSyntax(syntax);
    return *result;
}

UnpackedStructType::UnpackedStructType(Compilation& compilation) :
    Type(SymbolKind::UnpackedStructType, "", SourceLocation()), Scope(compilation, this) {
}

ConstantValue UnpackedStructType::getDefaultValueImpl() const {
    // TODO: implement this
    THROW_UNREACHABLE;
}

const Type& UnpackedStructType::fromSyntax(Compilation& compilation,
                                           const StructUnionTypeSyntax& syntax) {
    ASSERT(!syntax.packed);

    uint32_t fieldIndex = 0;
    auto result = compilation.emplace<UnpackedStructType>(compilation);
    for (auto member : syntax.members) {
        for (auto decl : member->declarators) {
            auto variable = compilation.emplace<FieldSymbol>(decl->name.valueText(),
                                                             decl->name.location(), fieldIndex);
            variable->setDeclaredType(*member->type);
            variable->setFromDeclarator(*decl);
            variable->setSyntax(*decl);

            result->addMember(*variable);
            fieldIndex++;
        }
    }

    result->setSyntax(syntax);
    return *result;
}

ConstantValue NullType::getDefaultValueImpl() const {
    return ConstantValue::NullPlaceholder{};
}

ConstantValue CHandleType::getDefaultValueImpl() const {
    return ConstantValue::NullPlaceholder{};
}

ConstantValue StringType::getDefaultValueImpl() const {
    // TODO: implement this
    THROW_UNREACHABLE;
}

ConstantValue EventType::getDefaultValueImpl() const {
    // TODO: implement this
    THROW_UNREACHABLE;
}

const ForwardingTypedefSymbol& ForwardingTypedefSymbol::fromSyntax(
    Compilation& compilation, const ForwardTypedefDeclarationSyntax& syntax) {
    Category category;
    switch (syntax.keyword.kind) {
        case TokenKind::EnumKeyword:
            category = Category::Enum;
            break;
        case TokenKind::StructKeyword:
            category = Category::Struct;
            break;
        case TokenKind::UnionKeyword:
            category = Category::Union;
            break;
        case TokenKind::ClassKeyword:
            category = Category::Class;
            break;
        default:
            category = Category::None;
            break;
    }
    auto result = compilation.emplace<ForwardingTypedefSymbol>(syntax.name.valueText(),
                                                               syntax.name.location(), category);
    result->setSyntax(syntax);
    return *result;
}

const ForwardingTypedefSymbol& ForwardingTypedefSymbol::fromSyntax(
    Compilation& compilation, const ForwardInterfaceClassTypedefDeclarationSyntax& syntax) {
    auto result = compilation.emplace<ForwardingTypedefSymbol>(
        syntax.name.valueText(), syntax.name.location(), Category::InterfaceClass);
    result->setSyntax(syntax);
    return *result;
}

void ForwardingTypedefSymbol::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!next)
        next = &decl;
    else
        next->addForwardDecl(decl);
}

void ForwardingTypedefSymbol::toJson(json& j) const {
    j["category"] = category; // TODO: tostring
}

const TypeAliasType& TypeAliasType::fromSyntax(Compilation& compilation,
                                               const TypedefDeclarationSyntax& syntax) {
    // TODO: unpacked dimensions
    auto result =
        compilation.emplace<TypeAliasType>(syntax.name.valueText(), syntax.name.location());
    result->targetType.setTypeSyntax(*syntax.type);
    result->setSyntax(syntax);
    return *result;
}

void TypeAliasType::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!firstForward)
        firstForward = &decl;
    else
        firstForward->addForwardDecl(decl);
}

void TypeAliasType::checkForwardDecls() const {
    ForwardingTypedefSymbol::Category category;
    switch (targetType.getType().kind) {
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
            category = ForwardingTypedefSymbol::Struct;
            break;
        case SymbolKind::EnumType:
            category = ForwardingTypedefSymbol::Enum;
            break;
        default:
            return;
    }

    const ForwardingTypedefSymbol* forward = firstForward;
    while (forward) {
        if (forward->category != ForwardingTypedefSymbol::None && forward->category != category) {
            auto& diag =
                getScope()->addDiag(DiagCode::ForwardTypedefDoesNotMatch, forward->location);
            switch (forward->category) {
                case ForwardingTypedefSymbol::Enum:
                    diag << "enum";
                    break;
                case ForwardingTypedefSymbol::Struct:
                    diag << "struct";
                    break;
                case ForwardingTypedefSymbol::Union:
                    diag << "union";
                    break;
                case ForwardingTypedefSymbol::Class:
                    diag << "class";
                    break;
                case ForwardingTypedefSymbol::InterfaceClass:
                    diag << "interface class";
                    break;
                default:
                    THROW_UNREACHABLE;
            }
            diag.addNote(DiagCode::NoteDeclarationHere, location);
            return;
        }
        forward = forward->getNextForwardDecl();
    }
}

ConstantValue TypeAliasType::getDefaultValueImpl() const {
    return targetType.getType().getDefaultValue();
}

NetType::NetType(NetKind netKind) :
    Type(SymbolKind::NetType, "", SourceLocation()), netKind(netKind) {
}

} // namespace slang
