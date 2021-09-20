//------------------------------------------------------------------------------
// AllTypes.cpp
// All type symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/types/AllTypes.h"

#include "slang/binding/BindContext.h"
#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/ClassSymbols.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/StackContainer.h"

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

string_view getName(PredefinedIntegerType::Kind kind) {
    switch (kind) {
        case PredefinedIntegerType::ShortInt: return "shortint"sv;
        case PredefinedIntegerType::Int: return "int"sv;
        case PredefinedIntegerType::LongInt: return "longint"sv;
        case PredefinedIntegerType::Byte: return "byte"sv;
        case PredefinedIntegerType::Integer: return "integer"sv;
        case PredefinedIntegerType::Time: return "time"sv;
        default: THROW_UNREACHABLE;
    }
}

string_view getName(ScalarType::Kind kind) {
    switch (kind) {
        case ScalarType::Bit: return "bit"sv;
        case ScalarType::Logic: return "logic"sv;
        case ScalarType::Reg: return "reg"sv;
        default: THROW_UNREACHABLE;
    }
}

string_view getName(FloatingType::Kind kind) {
    switch (kind) {
        case FloatingType::Real: return "real"sv;
        case FloatingType::ShortReal: return "shortreal"sv;
        case FloatingType::RealTime: return "realtime"sv;
        default: THROW_UNREACHABLE;
    }
}
// clang-format on

const Type& createPackedDims(const BindContext& context, const Type* type,
                             const SyntaxList<VariableDimensionSyntax>& dimensions) {
    size_t count = dimensions.size();
    for (size_t i = 0; i < count; i++) {
        auto& dimSyntax = *dimensions[count - i - 1];
        auto dim = context.evalPackedDimension(dimSyntax);
        if (!dim)
            return context.getCompilation().getErrorType();

        type = &PackedArrayType::fromSyntax(*context.scope, *type, *dim, dimSyntax);
    }

    return *type;
}

} // namespace

namespace slang {

const ErrorType ErrorType::Instance;

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
    if (kind == SymbolKind::PackedArrayType)
        return as<PackedArrayType>().range;

    return { int32_t(bitWidth - 1), 0 };
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
                                     bool isSigned, const BindContext& context) {
    // This is a simple integral vector (possibly of just one element).
    SmallVectorSized<std::pair<ConstantRange, const SyntaxNode*>, 4> dims;
    for (auto dimSyntax : dimensions) {
        auto dim = context.evalPackedDimension(*dimSyntax);
        if (!dim)
            return compilation.getErrorType();

        dims.emplace(*dim, dimSyntax);
    }

    if (dims.empty())
        return getPredefinedType(compilation, integerKind, isSigned);

    bitmask<IntegralFlags> flags;
    if (integerKind == SyntaxKind::RegType)
        flags |= IntegralFlags::Reg;
    if (isSigned)
        flags |= IntegralFlags::Signed;
    if (integerKind != SyntaxKind::BitType)
        flags |= IntegralFlags::FourState;

    if (dims.size() == 1 && dims[0].first.right == 0 && dims[0].first.left >= 0) {
        // if we have the common case of only one dimension and lsb == 0
        // then we can use the shared representation
        return compilation.getType(dims[0].first.width(), flags);
    }

    const Type* result = &compilation.getScalarType(flags);
    size_t count = dims.size();
    for (size_t i = 0; i < count; i++) {
        auto& pair = dims[count - i - 1];
        result = &PackedArrayType::fromSyntax(*context.scope, *result, pair.first, *pair.second);
    }

    return *result;
}

const Type& IntegralType::fromSyntax(Compilation& compilation, const IntegerTypeSyntax& syntax,
                                     const BindContext& context) {
    return fromSyntax(compilation, syntax.kind, syntax.dimensions,
                      syntax.signing.kind == TokenKind::SignedKeyword, context);
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
    IntegralType(SymbolKind::PredefinedIntegerType, getName(integerKind), SourceLocation(),
                 getWidth(integerKind), isSigned, getFourState(integerKind)),
    integerKind(integerKind) {
}

bool PredefinedIntegerType::isDefaultSigned(Kind integerKind) {
    return getSigned(integerKind);
}

ScalarType::ScalarType(Kind scalarKind) : ScalarType(scalarKind, false) {
}

ScalarType::ScalarType(Kind scalarKind, bool isSigned) :
    IntegralType(SymbolKind::ScalarType, getName(scalarKind), SourceLocation(), 1, isSigned,
                 scalarKind != Kind::Bit),
    scalarKind(scalarKind) {
}

FloatingType::FloatingType(Kind floatKind_) :
    Type(SymbolKind::FloatingType, getName(floatKind_), SourceLocation()), floatKind(floatKind_) {
}

ConstantValue FloatingType::getDefaultValueImpl() const {
    if (floatKind == ShortReal)
        return shortreal_t(0.0f);

    return real_t(0.0);
}

EnumType::EnumType(Compilation& compilation, SourceLocation loc, const Type& baseType_,
                   const BindContext& context) :
    IntegralType(SymbolKind::EnumType, "", loc, baseType_.getBitWidth(), baseType_.isSigned(),
                 baseType_.isFourState()),
    Scope(compilation, this), baseType(baseType_), systemId(compilation.getNextEnumSystemId()) {

    // Enum types don't live as members of the parent scope (they're "owned" by the declaration
    // containing them) but we hook up the parent pointer so that it can participate in name
    // lookups.
    setParent(*context.scope, context.lookupIndex);
}

static void checkEnumRange(const BindContext& context, const VariableDimensionSyntax& syntax) {
    auto checkExpr = [&](const ExpressionSyntax& expr) {
        if (expr.kind != SyntaxKind::IntegerLiteralExpression &&
            expr.kind != SyntaxKind::IntegerVectorExpression) {
            context.addDiag(diag::EnumRangeLiteral, expr.sourceRange());
        }
    };

    ASSERT(syntax.specifier && syntax.specifier->kind == SyntaxKind::RangeDimensionSpecifier);
    auto& sel = *syntax.specifier->as<RangeDimensionSpecifierSyntax>().selector;
    if (sel.kind == SyntaxKind::BitSelect) {
        auto& expr = *sel.as<BitSelectSyntax>().expr;
        checkExpr(expr);
    }
    else if (sel.kind == SyntaxKind::SimpleRangeSelect) {
        auto& range = sel.as<RangeSelectSyntax>();
        checkExpr(*range.left);
        checkExpr(*range.right);
    }
}

const Type& EnumType::fromSyntax(Compilation& compilation, const EnumTypeSyntax& syntax,
                                 const BindContext& context, const Type* typedefTarget) {
    const Type* base;
    const Type* cb;
    bitwidth_t bitWidth;

    if (!syntax.baseType) {
        // If no explicit base type is specified we default to an int.
        base = &compilation.getIntType();
        cb = base;
        bitWidth = cb->getBitWidth();
    }
    else {
        base = &compilation.getType(*syntax.baseType, context);
        cb = &base->getCanonicalType();
        if (!cb->isError() && !cb->isSimpleBitVector()) {
            context.addDiag(diag::InvalidEnumBase, syntax.baseType->getFirstToken().location())
                << *base;
            cb = &compilation.getErrorType();
        }

        bitWidth = cb->getBitWidth();
        if (bitWidth == 0)
            bitWidth = 1;
    }

    SVInt allOnes(bitWidth, 0, cb->isSigned());
    allOnes.setAllOnes();

    SVInt one(bitWidth, 1, cb->isSigned());
    ConstantValue previous;
    SourceRange previousRange;
    bool first = true;

    auto resultType =
        compilation.emplace<EnumType>(compilation, syntax.keyword.location(), *base, context);
    resultType->setSyntax(syntax);

    // Enum values must be unique; this set and lambda are used to check that.
    SmallMap<SVInt, SourceLocation, 8> usedValues;
    auto checkValue = [&usedValues, &context](const ConstantValue& cv, SourceLocation loc) {
        if (!cv)
            return;

        auto& value = cv.integer();
        auto pair = usedValues.emplace(value, loc);
        if (!pair.second) {
            auto& diag = context.addDiag(diag::EnumValueDuplicate, loc) << value;
            diag.addNote(diag::NotePreviousDefinition, pair.first->second);
        }
    };

    // For enumerands that have an initializer, set it up appropriately.
    auto setInitializer = [&](EnumValueSymbol& ev, const EqualsValueClauseSyntax& initializer) {
        ev.setInitializerSyntax(*initializer.expr, initializer.equals.location());

        first = false;
        previous = ev.getValue();
        previousRange = ev.getInitializer()->sourceRange;

        if (!previous || cb->isError())
            return;

        auto loc = previousRange.start();
        auto& value = previous.integer(); // checkEnumInitializer ensures previous is integral

        // An enumerated name with x or z assignments assigned to an enum with no explicit data type
        // or an explicit 2-state declaration shall be a syntax error.
        if (!base->isFourState() && value.hasUnknown()) {
            context.addDiag(diag::EnumValueUnknownBits, loc) << value << *base;
            ev.setValue(nullptr);
            previous = nullptr;
            return;
        }

        // Any enumeration encoding value that is outside the representable range of the enum base
        // type shall be an error. For an unsigned base type, this occurs if the cast truncates the
        // value and any of the discarded bits are nonzero. For a signed base type, this occurs if
        // the cast truncates the value and any of the discarded bits are not equal to the sign bit
        // of the result.
        if (value.getBitWidth() > bitWidth) {
            bool good = true;
            if (!base->isSigned()) {
                good = exactlyEqual(value[int32_t(bitWidth)], logic_t(false)) &&
                       value.isSignExtendedFrom(bitWidth);
            }
            else {
                good = value.isSignExtendedFrom(bitWidth - 1);
            }

            if (!good) {
                context.addDiag(diag::EnumValueOutOfRange, loc) << value << *base;
                ev.setValue(nullptr);
                previous = nullptr;
                return;
            }
        }

        // Implicit casting to base type to ensure value matches the underlying type.
        if (value.getBitWidth() != bitWidth) {
            auto cv = previous.convertToInt(bitWidth, base->isSigned(), base->isFourState());
            ev.setValue(cv);
            previous = std::move(cv);
        }
        else {
            if (!base->isFourState())
                value.flattenUnknowns();
            value.setSigned(base->isSigned());
        }

        checkValue(previous, loc);
    };

    // For enumerands that have no initializer, infer the value via this function.
    auto inferValue = [&](EnumValueSymbol& ev, SourceRange range) {
        auto loc = range.start();
        SVInt value;
        if (first) {
            value = SVInt(bitWidth, 0, cb->isSigned());
            first = false;
        }
        else if (!previous || cb->isError()) {
            return;
        }
        else {
            auto& prev = previous.integer();
            if (prev.hasUnknown()) {
                auto& diag = context.addDiag(diag::EnumIncrementUnknown, loc);
                diag << prev << *base << previousRange;
                previous = nullptr;
                return;
            }
            else if (prev == allOnes) {
                auto& diag = context.addDiag(diag::EnumValueOverflow, loc);
                diag << prev << *base << previousRange;
                previous = nullptr;
                return;
            }

            value = prev + one;
        }

        checkValue(value, loc);

        ev.setValue(value);
        previous = std::move(value);
        previousRange = range;
    };

    for (auto member : syntax.members) {
        if (member->dimensions.empty()) {
            auto& ev = EnumValueSymbol::fromSyntax(compilation, *member, *resultType, std::nullopt);
            resultType->addMember(ev);

            if (member->initializer)
                setInitializer(ev, *member->initializer);
            else
                inferValue(ev, member->sourceRange());
        }
        else {
            if (member->dimensions.size() > 1) {
                context.addDiag(diag::EnumRangeMultiDimensional, member->dimensions.sourceRange());
                return compilation.getErrorType();
            }

            auto range = context.evalUnpackedDimension(*member->dimensions[0]);
            if (!range)
                return compilation.getErrorType();

            // Range must be positive.
            if (!context.requirePositive(optional(range->left),
                                         member->dimensions[0]->sourceRange()) ||
                !context.requirePositive(optional(range->right),
                                         member->dimensions[0]->sourceRange())) {
                return compilation.getErrorType();
            }

            // Enum ranges must be integer literals.
            checkEnumRange(context, *member->dimensions[0]);

            // Set up the first element using the initializer. All other elements (if there are any)
            // don't get the initializer.
            int32_t index = range->left;
            {
                auto& ev = EnumValueSymbol::fromSyntax(compilation, *member, *resultType, index);
                resultType->addMember(ev);

                if (member->initializer)
                    setInitializer(ev, *member->initializer);
                else
                    inferValue(ev, member->sourceRange());
            }

            bool down = range->isLittleEndian();
            while (index != range->right) {
                index = down ? index - 1 : index + 1;

                auto& ev = EnumValueSymbol::fromSyntax(compilation, *member, *resultType, index);
                resultType->addMember(ev);

                inferValue(ev, member->sourceRange());
            }
        }
    }

    // If this enum is inside a typedef, override the types of each member to be
    // the typedef instead of the enum itself. This is done as a separate pass
    // so that we don't try to access the type of the enum values while we're
    // still in the middle of resolving it.
    if (typedefTarget) {
        for (auto& value : resultType->membersOfType<EnumValueSymbol>())
            const_cast<EnumValueSymbol&>(value).getDeclaredType()->setType(*typedefTarget);
    }

    return createPackedDims(context, resultType, syntax.dimensions);
}

EnumValueSymbol::EnumValueSymbol(string_view name, SourceLocation loc) :
    ValueSymbol(SymbolKind::EnumValue, name, loc, DeclaredTypeFlags::RequireConstant) {
}

EnumValueSymbol& EnumValueSymbol::fromSyntax(Compilation& compilation,
                                             const DeclaratorSyntax& syntax, const Type& type,
                                             optional<int32_t> index) {
    string_view name = syntax.name.valueText();
    if (index && !name.empty()) {
        ASSERT(*index >= 0);

        size_t sz = (size_t)snprintf(nullptr, 0, "%d", *index);
        char* mem = (char*)compilation.allocate(sz + name.size() + 1, 1);
        memcpy(mem, name.data(), name.size());
        snprintf(mem + name.size(), sz + 1, "%d", *index);

        name = string_view(mem, sz + name.size());
    }

    auto ev = compilation.emplace<EnumValueSymbol>(name, syntax.name.location());
    ev->setType(type);
    ev->setSyntax(syntax);

    return *ev;
}

const ConstantValue& EnumValueSymbol::getValue() const {
    if (!value) {
        // If no value has been explicitly set, try to set it
        // from our initializer.
        auto init = getInitializer();
        if (init) {
            auto scope = getParentScope();
            ASSERT(scope);

            BindContext ctx(*scope, LookupLocation::max);
            value = scope->getCompilation().allocConstant(ctx.eval(*init));
        }
        else {
            value = &ConstantValue::Invalid;
        }
    }
    return *value;
}

void EnumValueSymbol::setValue(ConstantValue newValue) {
    auto scope = getParentScope();
    ASSERT(scope);
    value = scope->getCompilation().allocConstant(std::move(newValue));
}

void EnumValueSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("value", getValue());
}

PackedArrayType::PackedArrayType(const Type& elementType, ConstantRange range) :
    IntegralType(SymbolKind::PackedArrayType, "", SourceLocation(),
                 elementType.getBitWidth() * range.width(), elementType.isSigned(),
                 elementType.isFourState()),
    elementType(elementType), range(range) {
}

const Type& PackedArrayType::fromSyntax(const Scope& scope, const Type& elementType,
                                        ConstantRange range, const SyntaxNode& syntax) {
    if (elementType.isError())
        return elementType;

    auto& comp = scope.getCompilation();
    if (!elementType.isIntegral()) {
        scope.addDiag(diag::PackedArrayNotIntegral, syntax.sourceRange()) << elementType;
        return comp.getErrorType();
    }

    auto width = checkedMulU32(elementType.getBitWidth(), range.width());
    if (!width || width > (uint32_t)SVInt::MAX_BITS) {
        uint64_t fullWidth = uint64_t(elementType.getBitWidth()) * range.width();
        scope.addDiag(diag::PackedArrayTooLarge, syntax.sourceRange())
            << fullWidth << (uint32_t)SVInt::MAX_BITS;
        return comp.getErrorType();
    }

    auto result = comp.emplace<PackedArrayType>(elementType, range);
    result->setSyntax(syntax);
    return *result;
}

FixedSizeUnpackedArrayType::FixedSizeUnpackedArrayType(const Type& elementType,
                                                       ConstantRange range) :
    Type(SymbolKind::FixedSizeUnpackedArrayType, "", SourceLocation()),
    elementType(elementType), range(range) {
}

const Type& FixedSizeUnpackedArrayType::fromDims(Compilation& compilation, const Type& elementType,
                                                 span<const ConstantRange> dimensions) {
    if (elementType.isError())
        return elementType;

    const Type* result = &elementType;
    size_t count = dimensions.size();
    for (size_t i = 0; i < count; i++) {
        result =
            compilation.emplace<FixedSizeUnpackedArrayType>(*result, dimensions[count - i - 1]);
    }

    return *result;
}

ConstantValue FixedSizeUnpackedArrayType::getDefaultValueImpl() const {
    return std::vector<ConstantValue>(range.width(), elementType.getDefaultValue());
}

DynamicArrayType::DynamicArrayType(const Type& elementType) :
    Type(SymbolKind::DynamicArrayType, "", SourceLocation()), elementType(elementType) {
}

ConstantValue DynamicArrayType::getDefaultValueImpl() const {
    return std::vector<ConstantValue>();
}

AssociativeArrayType::AssociativeArrayType(const Type& elementType, const Type* indexType) :
    Type(SymbolKind::AssociativeArrayType, "", SourceLocation()), elementType(elementType),
    indexType(indexType) {
}

ConstantValue AssociativeArrayType::getDefaultValueImpl() const {
    return AssociativeArray();
}

QueueType::QueueType(const Type& elementType, uint32_t maxBound) :
    Type(SymbolKind::QueueType, "", SourceLocation()), elementType(elementType),
    maxBound(maxBound) {
}

ConstantValue QueueType::getDefaultValueImpl() const {
    SVQueue result;
    result.maxBound = maxBound;
    return result;
}

PackedStructType::PackedStructType(Compilation& compilation, bitwidth_t bitWidth, bool isSigned,
                                   bool isFourState, SourceLocation loc,
                                   const BindContext& context) :
    IntegralType(SymbolKind::PackedStructType, "", loc, bitWidth, isSigned, isFourState),
    Scope(compilation, this), systemId(compilation.getNextStructSystemId()) {

    // Struct types don't live as members of the parent scope (they're "owned" by the declaration
    // containing them) but we hook up the parent pointer so that it can participate in name
    // lookups.
    setParent(*context.scope, context.lookupIndex);
}

const Type& PackedStructType::fromSyntax(Compilation& compilation,
                                         const StructUnionTypeSyntax& syntax,
                                         const BindContext& context) {
    ASSERT(syntax.packed);
    bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword;
    bool isFourState = false;
    bool issuedError = false;
    bitwidth_t bitWidth = 0;

    // We have to look at all the members up front to know our width and four-statedness.
    // We have to iterate in reverse because members are specified from MSB to LSB order.
    SmallVectorSized<const Symbol*, 8> members;
    for (auto member : make_reverse_range(syntax.members)) {
        const Type& type = compilation.getType(*member->type, context);
        isFourState |= type.isFourState();
        issuedError |= type.isError();

        if (!issuedError && !type.isIntegral()) {
            issuedError = true;
            auto& diag = context.addDiag(diag::PackedMemberNotIntegral,
                                         member->type->getFirstToken().location());
            diag << type;
            diag << member->type->sourceRange();
        }

        for (auto decl : member->declarators) {
            auto variable = compilation.emplace<FieldSymbol>(decl->name.valueText(),
                                                             decl->name.location(), bitWidth);
            variable->setType(type);
            variable->setSyntax(*decl);
            variable->setAttributes(*context.scope, member->attributes);
            members.append(variable);

            // Unpacked arrays are disallowed in packed structs.
            if (const Type& dimType = compilation.getType(type, decl->dimensions, context);
                dimType.isUnpackedArray() && !issuedError) {

                auto& diag = context.addDiag(diag::PackedMemberNotIntegral, decl->name.range());
                diag << dimType;
                diag << decl->dimensions.sourceRange();
                issuedError = true;
            }

            bitWidth += type.getBitWidth();

            if (decl->initializer) {
                auto& diag = context.addDiag(diag::PackedMemberHasInitializer,
                                             decl->initializer->equals.location());
                diag << decl->initializer->expr->sourceRange();
            }
        }
    }

    if (!bitWidth || issuedError)
        return compilation.getErrorType();

    auto structType = compilation.emplace<PackedStructType>(
        compilation, bitWidth, isSigned, isFourState, syntax.keyword.location(), context);
    structType->setSyntax(syntax);

    for (auto member : make_reverse_range(members))
        structType->addMember(*member);

    return createPackedDims(context, structType, syntax.dimensions);
}

UnpackedStructType::UnpackedStructType(Compilation& compilation, SourceLocation loc,
                                       const BindContext& context) :
    Type(SymbolKind::UnpackedStructType, "", loc),
    Scope(compilation, this), systemId(compilation.getNextStructSystemId()) {

    // Struct types don't live as members of the parent scope (they're "owned" by the declaration
    // containing them) but we hook up the parent pointer so that it can participate in name
    // lookups.
    setParent(*context.scope, context.lookupIndex);
}

ConstantValue UnpackedStructType::getDefaultValueImpl() const {
    std::vector<ConstantValue> elements;
    for (auto& field : membersOfType<FieldSymbol>())
        elements.emplace_back(field.getType().getDefaultValue());

    return elements;
}

const Type& UnpackedStructType::fromSyntax(const BindContext& context,
                                           const StructUnionTypeSyntax& syntax) {
    ASSERT(!syntax.packed);

    uint32_t fieldIndex = 0;
    auto& comp = context.getCompilation();
    auto result = comp.emplace<UnpackedStructType>(comp, syntax.keyword.location(), context);

    for (auto member : syntax.members) {
        RandMode randMode = RandMode::None;
        switch (member->randomQualifier.kind) {
            case TokenKind::RandKeyword:
                randMode = RandMode::Rand;
                break;
            case TokenKind::RandCKeyword:
                randMode = RandMode::RandC;
                break;
            default:
                break;
        }

        for (auto decl : member->declarators) {
            auto variable = comp.emplace<FieldSymbol>(decl->name.valueText(), decl->name.location(),
                                                      fieldIndex);
            variable->setDeclaredType(*member->type);
            variable->setFromDeclarator(*decl);
            variable->setAttributes(*context.scope, member->attributes);
            variable->randMode = randMode;

            if (randMode != RandMode::None)
                variable->getDeclaredType()->addFlags(DeclaredTypeFlags::Rand);

            result->addMember(*variable);
            fieldIndex++;

            // Force resolution of the type right away, otherwise nothing
            // is required to force it later.
            variable->getType();
            variable->getInitializer();
        }
    }

    result->setSyntax(syntax);
    return *result;
}

PackedUnionType::PackedUnionType(Compilation& compilation, bitwidth_t bitWidth, bool isSigned,
                                 bool isFourState, bool isTagged, uint32_t tagBits,
                                 SourceLocation loc, const BindContext& context) :
    IntegralType(SymbolKind::PackedUnionType, "", loc, bitWidth, isSigned, isFourState),
    Scope(compilation, this), systemId(compilation.getNextUnionSystemId()), isTagged(isTagged),
    tagBits(tagBits) {

    // Union types don't live as members of the parent scope (they're "owned" by the declaration
    // containing them) but we hook up the parent pointer so that it can participate in name
    // lookups.
    setParent(*context.scope, context.lookupIndex);
}

const Type& PackedUnionType::fromSyntax(Compilation& compilation,
                                        const StructUnionTypeSyntax& syntax,
                                        const BindContext& context) {
    ASSERT(syntax.packed);
    bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword;
    bool isTagged = syntax.tagged.valid();
    bool isFourState = false;
    bool issuedError = false;
    bitwidth_t bitWidth = 0;
    uint32_t fieldIndex = 0;

    // We have to look at all the members up front to know our width and four-statedness.
    SmallVectorSized<const Symbol*, 8> members;
    for (auto member : syntax.members) {
        const Type& type = compilation.getType(*member->type, context);
        isFourState |= type.isFourState();
        issuedError |= type.isError();

        if (!issuedError && !type.isIntegral() && (!isTagged || !type.isVoid())) {
            issuedError = true;
            auto& diag = context.addDiag(diag::PackedMemberNotIntegral,
                                         member->type->getFirstToken().location());
            diag << type;
            diag << member->type->sourceRange();
        }

        for (auto decl : member->declarators) {
            auto name = decl->name;
            auto variable =
                compilation.emplace<FieldSymbol>(name.valueText(), name.location(), fieldIndex++);
            variable->setType(type);
            variable->setSyntax(*decl);
            variable->setAttributes(*context.scope, member->attributes);
            members.append(variable);

            // Unpacked arrays are disallowed in packed unions.
            if (const Type& dimType = compilation.getType(type, decl->dimensions, context);
                dimType.isUnpackedArray() && !issuedError) {

                auto& diag = context.addDiag(diag::PackedMemberNotIntegral, decl->name.range());
                diag << dimType;
                diag << decl->dimensions.sourceRange();
                issuedError = true;
            }

            if (!bitWidth) {
                bitWidth = type.getBitWidth();
            }
            else if (isTagged) {
                // In tagged unions the members don't all have to have the same width.
                bitWidth = std::max(bitWidth, type.getBitWidth());
            }
            else if (bitWidth != type.getBitWidth() && !issuedError && !name.valueText().empty()) {
                auto& diag = context.addDiag(diag::PackedUnionWidthMismatch, name.range());
                diag << name.valueText() << type.getBitWidth() << bitWidth;
                issuedError = true;
            }

            if (decl->initializer) {
                auto& diag = context.addDiag(diag::PackedMemberHasInitializer,
                                             decl->initializer->equals.location());
                diag << decl->initializer->expr->sourceRange();
            }
        }
    }

    // In tagged unions the tag contributes to the total number of packed bits.
    uint32_t tagBits = 0;
    if (isTagged) {
        tagBits = clog2(members.size());
        bitWidth += tagBits;
    }

    if (!bitWidth || issuedError)
        return compilation.getErrorType();

    auto unionType =
        compilation.emplace<PackedUnionType>(compilation, bitWidth, isSigned, isFourState, isTagged,
                                             tagBits, syntax.keyword.location(), context);
    unionType->setSyntax(syntax);

    for (auto member : members)
        unionType->addMember(*member);

    return createPackedDims(context, unionType, syntax.dimensions);
}

UnpackedUnionType::UnpackedUnionType(Compilation& compilation, bool isTagged, SourceLocation loc,
                                     const BindContext& context) :
    Type(SymbolKind::UnpackedUnionType, "", loc),
    Scope(compilation, this), systemId(compilation.getNextUnionSystemId()), isTagged(isTagged) {

    // Union types don't live as members of the parent scope (they're "owned" by the declaration
    // containing them) but we hook up the parent pointer so that it can participate in name
    // lookups.
    setParent(*context.scope, context.lookupIndex);
}

ConstantValue UnpackedUnionType::getDefaultValueImpl() const {
    auto range = membersOfType<FieldSymbol>();
    auto it = range.begin();
    if (it == range.end())
        return nullptr;

    SVUnion u;
    u.value = it->getType().getDefaultValue();

    // Tagged unions start out with no active member.
    if (!isTagged)
        u.activeMember = 0;

    return u;
}

const Type& UnpackedUnionType::fromSyntax(const BindContext& context,
                                          const StructUnionTypeSyntax& syntax) {
    ASSERT(!syntax.packed);

    auto& comp = context.getCompilation();
    bool isTagged = syntax.tagged.valid();
    auto result =
        comp.emplace<UnpackedUnionType>(comp, isTagged, syntax.keyword.location(), context);

    uint32_t fieldIndex = 0;
    for (auto member : syntax.members) {
        for (auto decl : member->declarators) {
            auto variable = comp.emplace<FieldSymbol>(decl->name.valueText(), decl->name.location(),
                                                      fieldIndex++);
            variable->setDeclaredType(*member->type);
            variable->setFromDeclarator(*decl);
            variable->setAttributes(*context.scope, member->attributes);

            result->addMember(*variable);

            auto& varType = variable->getType();
            if (!isTagged && (varType.isCHandle() || varType.isDynamicallySizedArray()))
                context.addDiag(diag::InvalidUnionMember, decl->name.range()) << varType;
            else if (varType.isVirtualInterface())
                context.addDiag(diag::VirtualInterfaceUnionMember, decl->name.range());

            // Force resolution of the initializer right away, otherwise nothing
            // is required to force it later.
            variable->getInitializer();
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
    return ""s;
}

ConstantValue EventType::getDefaultValueImpl() const {
    return ConstantValue::NullPlaceholder{};
}

const Type& VirtualInterfaceType::fromSyntax(const BindContext& context,
                                             const VirtualInterfaceTypeSyntax& syntax) {
    auto& comp = context.getCompilation();
    auto ifaceName = syntax.name.valueText();
    if (ifaceName.empty())
        return comp.getErrorType();

    auto definition = comp.getDefinition(ifaceName, *context.scope);
    if (!definition || definition->definitionKind != DefinitionKind::Interface) {
        context.addDiag(diag::UnknownInterface, syntax.name.range()) << ifaceName;
        return comp.getErrorType();
    }

    auto loc = syntax.name.location();
    auto iface = InstanceBodySymbol::fromDefinition(context, loc, *definition, syntax.parameters);
    if (!iface)
        return comp.getErrorType();

    const ModportSymbol* modport = nullptr;
    string_view modportName = syntax.modport ? syntax.modport->member.valueText() : ""sv;
    if (!modportName.empty()) {
        auto sym = iface->find(modportName);
        if (!sym || sym->kind != SymbolKind::Modport) {
            ASSERT(syntax.modport);
            auto& diag = context.addDiag(diag::NotAModport, syntax.modport->member.range());
            diag << modportName;
            diag << definition->name;
        }
        else {
            modport = &sym->as<ModportSymbol>();
        }
    }

    return *comp.emplace<VirtualInterfaceType>(*iface, modport, loc);
}

ConstantValue VirtualInterfaceType::getDefaultValueImpl() const {
    return ConstantValue::NullPlaceholder{};
}

ForwardingTypedefSymbol& ForwardingTypedefSymbol::fromSyntax(
    const Scope& scope, const ForwardTypedefDeclarationSyntax& syntax) {

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

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<ForwardingTypedefSymbol>(syntax.name.valueText(),
                                                        syntax.name.location(), category);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    return *result;
}

ForwardingTypedefSymbol& ForwardingTypedefSymbol::fromSyntax(
    const Scope& scope, const ForwardInterfaceClassTypedefDeclarationSyntax& syntax) {

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<ForwardingTypedefSymbol>(
        syntax.name.valueText(), syntax.name.location(), Category::InterfaceClass);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    return *result;
}

ForwardingTypedefSymbol& ForwardingTypedefSymbol::fromSyntax(
    const Scope& scope, const ClassPropertyDeclarationSyntax& syntax) {

    ForwardingTypedefSymbol* result;
    if (syntax.declaration->kind == SyntaxKind::ForwardInterfaceClassTypedefDeclaration) {
        result = &fromSyntax(
            scope, syntax.declaration->as<ForwardInterfaceClassTypedefDeclarationSyntax>());
    }
    else {
        result = &fromSyntax(scope, syntax.declaration->as<ForwardTypedefDeclarationSyntax>());
    }

    for (Token qual : syntax.qualifiers) {
        switch (qual.kind) {
            case TokenKind::LocalKeyword:
                result->visibility = Visibility::Local;
                break;
            case TokenKind::ProtectedKeyword:
                result->visibility = Visibility::Protected;
                break;
            default:
                // Everything else is not allowed on typedefs; the parser will issue
                // a diagnostic so just ignore them here.
                break;
        }
    }

    result->setAttributes(scope, syntax.attributes);
    return *result;
}

void ForwardingTypedefSymbol::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!next)
        next = &decl;
    else
        next->addForwardDecl(decl);
}

void ForwardingTypedefSymbol::checkType(Category checkCategory, Visibility checkVisibility,
                                        SourceLocation declLoc) const {
    if (category != None && checkCategory != None && category != checkCategory) {
        auto& diag = getParentScope()->addDiag(diag::ForwardTypedefDoesNotMatch, location);
        switch (category) {
            case ForwardingTypedefSymbol::Enum:
                diag << "enum"sv;
                break;
            case ForwardingTypedefSymbol::Struct:
                diag << "struct"sv;
                break;
            case ForwardingTypedefSymbol::Union:
                diag << "union"sv;
                break;
            case ForwardingTypedefSymbol::Class:
                diag << "class"sv;
                break;
            case ForwardingTypedefSymbol::InterfaceClass:
                diag << "interface class"sv;
                break;
            default:
                THROW_UNREACHABLE;
        }
        diag.addNote(diag::NoteDeclarationHere, declLoc);
        return;
    }

    if (visibility && visibility != checkVisibility) {
        auto& diag = getParentScope()->addDiag(diag::ForwardTypedefVisibility, location);
        diag.addNote(diag::NoteDeclarationHere, declLoc);
        return;
    }

    if (next)
        next->checkType(checkCategory, checkVisibility, declLoc);
}

void ForwardingTypedefSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("category", toString(category));
    if (next)
        serializer.write("next", *next);
}

TypeAliasType::TypeAliasType(string_view name, SourceLocation loc) :
    Type(SymbolKind::TypeAlias, name, loc), targetType(*this, DeclaredTypeFlags::TypedefTarget) {
    canonical = nullptr;
}

TypeAliasType& TypeAliasType::fromSyntax(const Scope& scope,
                                         const TypedefDeclarationSyntax& syntax) {
    // TODO: interface based typedefs
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<TypeAliasType>(syntax.name.valueText(), syntax.name.location());
    result->targetType.setTypeSyntax(*syntax.type);
    result->targetType.setDimensionSyntax(syntax.dimensions);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    return *result;
}

TypeAliasType& TypeAliasType::fromSyntax(const Scope& scope,
                                         const ClassPropertyDeclarationSyntax& syntax) {
    auto& result = fromSyntax(scope, syntax.declaration->as<TypedefDeclarationSyntax>());
    for (Token qual : syntax.qualifiers) {
        switch (qual.kind) {
            case TokenKind::LocalKeyword:
                result.visibility = Visibility::Local;
                break;
            case TokenKind::ProtectedKeyword:
                result.visibility = Visibility::Protected;
                break;
            default:
                // Everything else is not allowed on typedefs; the parser will issue
                // a diagnostic so just ignore them here.
                break;
        }
    }

    result.setAttributes(scope, syntax.attributes);
    return result;
}

void TypeAliasType::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!firstForward)
        firstForward = &decl;
    else
        firstForward->addForwardDecl(decl);
}

void TypeAliasType::checkForwardDecls() const {
    auto& ct = targetType.getType().getCanonicalType();
    ForwardingTypedefSymbol::Category category;
    switch (ct.kind) {
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
            category = ForwardingTypedefSymbol::Struct;
            break;
        case SymbolKind::PackedUnionType:
        case SymbolKind::UnpackedUnionType:
            category = ForwardingTypedefSymbol::Union;
            break;
        case SymbolKind::EnumType:
            category = ForwardingTypedefSymbol::Enum;
            break;
        case SymbolKind::ClassType:
            category = ForwardingTypedefSymbol::Class;
            if (ct.as<ClassType>().isInterface)
                category = ForwardingTypedefSymbol::InterfaceClass;
            break;
        default:
            category = ForwardingTypedefSymbol::None;
            break;
    }

    if (firstForward)
        firstForward->checkType(category, visibility, location);
}

ConstantValue TypeAliasType::getDefaultValueImpl() const {
    return targetType.getType().getDefaultValue();
}

void TypeAliasType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("target", targetType.getType());
    if (firstForward)
        serializer.write("forward", *firstForward);
}

} // namespace slang
