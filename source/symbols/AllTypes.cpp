//------------------------------------------------------------------------------
// AllTypes.cpp
// All type symbol definitions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/symbols/AllTypes.h"

#include "slang/binding/ConstantValue.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/symbols/TypePrinter.h"
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
// clang-format on

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
                                     bool isSigned, LookupLocation location, const Scope& scope) {
    // This is a simple integral vector (possibly of just one element).
    BindContext context(scope, location);
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

    if (dims.size() == 1 && dims[0].first.right == 0) {
        // if we have the common case of only one dimension and lsb == 0
        // then we can use the shared representation
        return compilation.getType(dims[0].first.width(), flags);
    }

    const Type* result = &compilation.getScalarType(flags);
    size_t count = dims.size();
    for (size_t i = 0; i < count; i++) {
        auto& pair = dims[count - i - 1];
        result = &PackedArrayType::fromSyntax(compilation, *result, pair.first, *pair.second);
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
    if (floatKind == ShortReal)
        return shortreal_t(0.0f);

    return real_t(0.0);
}

EnumType::EnumType(Compilation& compilation, SourceLocation loc, const Type& baseType_,
                   LookupLocation lookupLocation) :
    IntegralType(SymbolKind::EnumType, "", loc, baseType_.getBitWidth(), baseType_.isSigned(),
                 baseType_.isFourState()),
    Scope(compilation, this), baseType(baseType_) {

    // Enum types don't live as members of the parent scope (they're "owned" by the declaration
    // containing them) but we hook up the parent pointer so that it can participate in name
    // lookups.
    auto scope = lookupLocation.getScope();
    ASSERT(scope);
    setParent(*scope, lookupLocation.getIndex());
}

const Type& EnumType::fromSyntax(Compilation& compilation, const EnumTypeSyntax& syntax,
                                 LookupLocation location, const Scope& scope, bool forceSigned) {
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
        base = &compilation.getType(*syntax.baseType, location, scope, forceSigned);
        cb = &base->getCanonicalType();
        if (!cb->isError() && !cb->isSimpleBitVector()) {
            scope.addDiag(diag::InvalidEnumBase, syntax.baseType->getFirstToken().location())
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
        compilation.emplace<EnumType>(compilation, syntax.keyword.location(), *base, location);
    resultType->setSyntax(syntax);

    // Enum values must be unique; this set and lambda are used to check that.
    SmallMap<SVInt, SourceLocation, 8> usedValues;
    auto checkValue = [&usedValues, &scope](const ConstantValue& cv, SourceLocation loc) {
        if (!cv)
            return;

        auto& value = cv.integer();
        auto pair = usedValues.emplace(value, loc);
        if (!pair.second) {
            auto& diag = scope.addDiag(diag::EnumValueDuplicate, loc) << value;
            diag.addNote(diag::NotePreviousDefinition, pair.first->second);
        }
    };

    // For enumerands that have an initializer, set it up appropriately.
    auto setInitializer = [&](EnumValueSymbol& ev, const EqualsValueClauseSyntax& initializer) {
        ev.setInitializerSyntax(*initializer.expr, initializer.equals.location());

        first = false;
        previous = ev.getConstantValue();
        previousRange = ev.getInitializer()->sourceRange;

        checkValue(previous, previousRange.start());
    };

    // For enumerands that have no initializer, infer the value via this function.
    auto inferValue = [&](EnumValueSymbol& ev, SourceRange range) {
        auto loc = range.start();
        SVInt value;
        if (first) {
            value = SVInt(bitWidth, 0, cb->isSigned());
            first = false;
        }
        else if (!previous) {
            return;
        }
        else {
            auto& prev = previous.integer();
            if (prev.hasUnknown()) {
                auto& diag = scope.addDiag(diag::EnumIncrementUnknown, loc);
                diag << prev << *base << previousRange;
                previous = nullptr;
                return;
            }
            else if (prev == allOnes) {
                auto& diag = scope.addDiag(diag::EnumValueOverflow, loc);
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

    BindContext context(scope, location);

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
                scope.addDiag(diag::EnumRangeMultiDimensional, member->dimensions.sourceRange());
                return compilation.getErrorType();
            }

            auto range = context.evalUnpackedDimension(*member->dimensions[0]);
            if (!range)
                return compilation.getErrorType();

            // Range must be positive.
            if (!context.requirePositive(range->left, member->dimensions[0]->sourceRange()) ||
                !context.requirePositive(range->right, member->dimensions[0]->sourceRange())) {
                return compilation.getErrorType();
            }

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

    return *resultType;
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
    return value ? *value : getConstantValue();
}

void EnumValueSymbol::setValue(ConstantValue newValue) {
    auto scope = getParentScope();
    ASSERT(scope);
    value = scope->getCompilation().allocConstant(std::move(newValue));
}

void EnumValueSymbol::serializeTo(ASTSerializer& serializer) const {
    if (value)
        serializer.write("value", *value);
}

PackedArrayType::PackedArrayType(const Type& elementType, ConstantRange range) :
    IntegralType(SymbolKind::PackedArrayType, "", SourceLocation(),
                 elementType.getBitWidth() * range.width(), elementType.isSigned(),
                 elementType.isFourState()),
    elementType(elementType), range(range) {
}

const Type& PackedArrayType::fromSyntax(Compilation& compilation, const Type& elementType,
                                        ConstantRange range, const SyntaxNode& syntax) {
    if (elementType.isError())
        return elementType;

    // TODO: check bitwidth of array
    // TODO: ensure integral
    auto result = compilation.emplace<PackedArrayType>(elementType, range);
    result->setSyntax(syntax);
    return *result;
}

UnpackedArrayType::UnpackedArrayType(const Type& elementType, ConstantRange range) :
    Type(SymbolKind::UnpackedArrayType, "", SourceLocation()), elementType(elementType),
    range(range) {
}

const Type& UnpackedArrayType::fromSyntax(Compilation& compilation, const Type& elementType,
                                          LookupLocation location, const Scope& scope,
                                          const SyntaxList<VariableDimensionSyntax>& dimensions) {
    if (elementType.isError())
        return elementType;

    BindContext context(scope, location);

    const Type* result = &elementType;
    size_t count = dimensions.size();
    for (size_t i = 0; i < count; i++) {
        // TODO: handle other kinds of unpacked arrays
        EvaluatedDimension dim = context.evalDimension(*dimensions[count - i - 1], true);
        if (!dim.isRange())
            return compilation.getErrorType();

        auto unpacked = compilation.emplace<UnpackedArrayType>(*result, dim.range);
        unpacked->setSyntax(*dimensions[count - i - 1]);
        result = unpacked;
    }

    return *result;
}

ConstantValue UnpackedArrayType::getDefaultValueImpl() const {
    return std::vector<ConstantValue>(range.width(), elementType.getDefaultValue());
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
            auto& diag = scope.addDiag(diag::PackedMemberNotIntegral,
                                       member->type->getFirstToken().location());
            diag << type;
            diag << member->type->sourceRange();
        }

        for (auto decl : member->declarators) {
            auto variable = compilation.emplace<FieldSymbol>(decl->name.valueText(),
                                                             decl->name.location(), bitWidth);
            variable->setType(type);
            variable->setSyntax(*decl);
            variable->setAttributes(scope, member->attributes);
            members.append(variable);

            // Unpacked arrays are disallowed in packed structs.
            if (const Type& dimType = compilation.getType(type, decl->dimensions, location, scope);
                dimType.isUnpackedArray() && !issuedError) {

                auto& diag = scope.addDiag(diag::PackedMemberNotIntegral, decl->name.range());
                diag << dimType;
                diag << decl->dimensions.sourceRange();
                issuedError = true;
            }

            bitWidth += type.getBitWidth();

            if (decl->initializer) {
                auto& diag = scope.addDiag(diag::PackedMemberHasInitializer,
                                           decl->initializer->equals.location());
                diag << decl->initializer->expr->sourceRange();
            }
        }
    }

    // TODO: cannot be empty
    if (!bitWidth)
        return compilation.getErrorType();

    auto structType =
        compilation.emplace<PackedStructType>(compilation, bitWidth, isSigned, isFourState);
    for (auto member : make_reverse_range(members))
        structType->addMember(*member);

    structType->setSyntax(syntax);

    const Type* result = structType;
    BindContext context(scope, location);

    size_t count = syntax.dimensions.size();
    for (size_t i = 0; i < count; i++) {
        auto& dimSyntax = *syntax.dimensions[count - i - 1];
        auto dim = context.evalPackedDimension(dimSyntax);
        if (!dim)
            return compilation.getErrorType();

        result = &PackedArrayType::fromSyntax(compilation, *result, *dim, dimSyntax);
    }

    return *result;
}

UnpackedStructType::UnpackedStructType(Compilation& compilation) :
    Type(SymbolKind::UnpackedStructType, "", SourceLocation()), Scope(compilation, this) {
}

ConstantValue UnpackedStructType::getDefaultValueImpl() const {
    std::vector<ConstantValue> elements;
    for (auto& field : membersOfType<FieldSymbol>())
        elements.emplace_back(field.getType().getDefaultValue());

    return elements;
}

const Type& UnpackedStructType::fromSyntax(const Scope& scope,
                                           const StructUnionTypeSyntax& syntax) {
    ASSERT(!syntax.packed);

    uint32_t fieldIndex = 0;
    auto& comp = scope.getCompilation();
    auto result = comp.emplace<UnpackedStructType>(comp);
    for (auto member : syntax.members) {
        for (auto decl : member->declarators) {
            auto variable = comp.emplace<FieldSymbol>(decl->name.valueText(), decl->name.location(),
                                                      fieldIndex);
            variable->setDeclaredType(*member->type);
            variable->setFromDeclarator(*decl);
            variable->setAttributes(scope, member->attributes);

            result->addMember(*variable);
            fieldIndex++;
        }
    }

    // TODO: error if dimensions
    // TODO: error if signing
    // TODO: check for void types
    // TODO: cannot be empty

    result->setSyntax(syntax);
    return *result;
}

PackedUnionType::PackedUnionType(Compilation& compilation, bitwidth_t bitWidth, bool isSigned,
                                 bool isFourState) :
    IntegralType(SymbolKind::PackedUnionType, "", SourceLocation(), bitWidth, isSigned,
                 isFourState),
    Scope(compilation, this) {
}

const Type& PackedUnionType::fromSyntax(Compilation& compilation,
                                        const StructUnionTypeSyntax& syntax,
                                        LookupLocation location, const Scope& scope,
                                        bool forceSigned) {
    ASSERT(syntax.packed);
    bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword || forceSigned;
    bool isFourState = false;
    bitwidth_t bitWidth = 0;

    // We have to look at all the members up front to know our width and four-statedness.
    SmallVectorSized<const Symbol*, 8> members;
    for (auto member : syntax.members) {
        const Type& type = compilation.getType(*member->type, location, scope);
        isFourState |= type.isFourState();

        bool issuedError = false;
        if (!type.isIntegral() && !type.isError()) {
            issuedError = true;
            auto& diag = scope.addDiag(diag::PackedMemberNotIntegral,
                                       member->type->getFirstToken().location());
            diag << type;
            diag << member->type->sourceRange();
        }

        for (auto decl : member->declarators) {
            auto variable =
                compilation.emplace<FieldSymbol>(decl->name.valueText(), decl->name.location(), 0u);
            variable->setType(type);
            variable->setSyntax(*decl);
            variable->setAttributes(scope, member->attributes);
            members.append(variable);

            // Unpacked arrays are disallowed in packed unions.
            if (const Type& dimType = compilation.getType(type, decl->dimensions, location, scope);
                dimType.isUnpackedArray() && !issuedError) {

                auto& diag = scope.addDiag(diag::PackedMemberNotIntegral, decl->name.range());
                diag << dimType;
                diag << decl->dimensions.sourceRange();
                issuedError = true;
            }

            if (!bitWidth)
                bitWidth = type.getBitWidth();
            else if (bitWidth != type.getBitWidth() && !issuedError) {
                scope.addDiag(diag::PackedUnionWidthMismatch, decl->name.range());
                issuedError = true;
            }

            if (decl->initializer) {
                auto& diag = scope.addDiag(diag::PackedMemberHasInitializer,
                                           decl->initializer->equals.location());
                diag << decl->initializer->expr->sourceRange();
            }
        }
    }

    // TODO: cannot be empty
    if (!bitWidth)
        return compilation.getErrorType();

    auto unionType =
        compilation.emplace<PackedUnionType>(compilation, bitWidth, isSigned, isFourState);
    for (auto member : members)
        unionType->addMember(*member);

    unionType->setSyntax(syntax);

    const Type* result = unionType;
    BindContext context(scope, location);

    size_t count = syntax.dimensions.size();
    for (size_t i = 0; i < count; i++) {
        auto& dimSyntax = *syntax.dimensions[count - i - 1];
        auto dim = context.evalPackedDimension(dimSyntax);
        if (!dim)
            return compilation.getErrorType();

        result = &PackedArrayType::fromSyntax(compilation, *result, *dim, dimSyntax);
    }

    return *result;
}

UnpackedUnionType::UnpackedUnionType(Compilation& compilation) :
    Type(SymbolKind::UnpackedUnionType, "", SourceLocation()), Scope(compilation, this) {
}

ConstantValue UnpackedUnionType::getDefaultValueImpl() const {
    auto range = membersOfType<FieldSymbol>();
    auto it = range.begin();
    if (it == range.end())
        return nullptr;

    return it->getType().getDefaultValue();
}

const Type& UnpackedUnionType::fromSyntax(const Scope& scope, const StructUnionTypeSyntax& syntax) {
    ASSERT(!syntax.packed);

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<UnpackedUnionType>(comp);
    for (auto member : syntax.members) {
        for (auto decl : member->declarators) {
            auto variable =
                comp.emplace<FieldSymbol>(decl->name.valueText(), decl->name.location(), 0u);
            variable->setDeclaredType(*member->type);
            variable->setFromDeclarator(*decl);
            variable->setAttributes(scope, member->attributes);

            result->addMember(*variable);
        }
    }

    // TODO: error if dimensions
    // TODO: error if signing
    // TODO: check for void types
    // TODO: cannot be empty

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

const ForwardingTypedefSymbol& ForwardingTypedefSymbol::fromSyntax(
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

const ForwardingTypedefSymbol& ForwardingTypedefSymbol::fromSyntax(
    const Scope& scope, const ForwardInterfaceClassTypedefDeclarationSyntax& syntax) {

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<ForwardingTypedefSymbol>(
        syntax.name.valueText(), syntax.name.location(), Category::InterfaceClass);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    return *result;
}

void ForwardingTypedefSymbol::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!next)
        next = &decl;
    else
        next->addForwardDecl(decl);
}

void ForwardingTypedefSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("category", toString(category));
    if (next)
        serializer.write("next", *next);
}

const TypeAliasType& TypeAliasType::fromSyntax(const Scope& scope,
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
        case SymbolKind::PackedUnionType:
        case SymbolKind::UnpackedUnionType:
            category = ForwardingTypedefSymbol::Union;
            break;
        case SymbolKind::EnumType:
            category = ForwardingTypedefSymbol::Enum;
            break;
        default:
            // TODO:
            return;
    }

    const ForwardingTypedefSymbol* forward = firstForward;
    while (forward) {
        if (forward->category != ForwardingTypedefSymbol::None && forward->category != category) {
            auto& diag =
                getParentScope()->addDiag(diag::ForwardTypedefDoesNotMatch, forward->location);
            switch (forward->category) {
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
            diag.addNote(diag::NoteDeclarationHere, location);
            return;
        }
        forward = forward->getNextForwardDecl();
    }
}

ConstantValue TypeAliasType::getDefaultValueImpl() const {
    return targetType.getType().getDefaultValue();
}

void TypeAliasType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("target", targetType.getType());
    if (firstForward)
        serializer.write("forward", *firstForward);
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
