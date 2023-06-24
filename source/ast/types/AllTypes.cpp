//------------------------------------------------------------------------------
// AllTypes.cpp
// All type symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/types/AllTypes.h"

#include "slang/ast/ASTContext.h"
#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/numeric/MathUtils.h"
#include "slang/syntax/AllSyntax.h"

namespace {

using namespace slang;
using namespace slang::syntax;
using namespace slang::ast;

// clang-format off
bitwidth_t getWidth(PredefinedIntegerType::Kind kind) {
    switch (kind) {
        case PredefinedIntegerType::ShortInt: return 16;
        case PredefinedIntegerType::Int: return 32;
        case PredefinedIntegerType::LongInt: return 64;
        case PredefinedIntegerType::Byte: return 8;
        case PredefinedIntegerType::Integer: return 32;
        case PredefinedIntegerType::Time: return 64;
        default: SLANG_UNREACHABLE;
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
        default: SLANG_UNREACHABLE;
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
        default: SLANG_UNREACHABLE;
    }
}

std::string_view getName(PredefinedIntegerType::Kind kind) {
    switch (kind) {
        case PredefinedIntegerType::ShortInt: return "shortint"sv;
        case PredefinedIntegerType::Int: return "int"sv;
        case PredefinedIntegerType::LongInt: return "longint"sv;
        case PredefinedIntegerType::Byte: return "byte"sv;
        case PredefinedIntegerType::Integer: return "integer"sv;
        case PredefinedIntegerType::Time: return "time"sv;
        default: SLANG_UNREACHABLE;
    }
}

std::string_view getName(ScalarType::Kind kind) {
    switch (kind) {
        case ScalarType::Bit: return "bit"sv;
        case ScalarType::Logic: return "logic"sv;
        case ScalarType::Reg: return "reg"sv;
        default: SLANG_UNREACHABLE;
    }
}

std::string_view getName(FloatingType::Kind kind) {
    switch (kind) {
        case FloatingType::Real: return "real"sv;
        case FloatingType::ShortReal: return "shortreal"sv;
        case FloatingType::RealTime: return "realtime"sv;
        default: SLANG_UNREACHABLE;
    }
}
// clang-format on

const Type& createPackedDims(const ASTContext& context, const Type* type,
                             const SyntaxList<VariableDimensionSyntax>& dimensions) {
    size_t count = dimensions.size();
    for (size_t i = 0; i < count; i++) {
        auto& dimSyntax = *dimensions[count - i - 1];
        auto dim = context.evalPackedDimension(dimSyntax);
        type = &PackedArrayType::fromSyntax(*context.scope, *type, dim, dimSyntax);
    }

    return *type;
}

} // namespace

namespace slang::ast {

using namespace parsing;
using namespace syntax;

const ErrorType ErrorType::Instance;

IntegralType::IntegralType(SymbolKind kind, std::string_view name, SourceLocation loc,
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

    return {int32_t(bitWidth - 1), 0};
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
                                     std::span<const VariableDimensionSyntax* const> dimensions,
                                     bool isSigned, const ASTContext& context) {
    // This is a simple integral vector (possibly of just one element).
    SmallVector<std::pair<EvaluatedDimension, const SyntaxNode*>, 4> dims;
    for (auto dimSyntax : dimensions) {
        auto dim = context.evalPackedDimension(*dimSyntax);
        dims.emplace_back(dim, dimSyntax);
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

    if (dims.size() == 1 && dims[0].first.isRange()) {
        auto range = dims[0].first.range;
        if (range.right == 0 && range.left >= 0) {
            // if we have the common case of only one dimension and lsb == 0
            // then we can use the shared representation
            return compilation.getType(range.width(), flags);
        }
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
                                     const ASTContext& context) {
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
                   const ASTContext& context) :
    IntegralType(SymbolKind::EnumType, "", loc, baseType_.getBitWidth(), baseType_.isSigned(),
                 baseType_.isFourState()),
    Scope(compilation, this), baseType(baseType_), systemId(compilation.getNextEnumSystemId()) {

    // Enum types don't live as members of the parent scope (they're "owned" by the declaration
    // containing them) but we hook up the parent pointer so that it can participate in name
    // lookups.
    setParent(*context.scope, context.lookupIndex);
}

static void checkEnumRange(const ASTContext& context, const VariableDimensionSyntax& syntax) {
    auto checkExpr = [&](const ExpressionSyntax& expr) {
        if (expr.kind != SyntaxKind::IntegerLiteralExpression &&
            expr.kind != SyntaxKind::IntegerVectorExpression) {
            context.addDiag(diag::EnumRangeLiteral, expr.sourceRange());
        }
    };

    SLANG_ASSERT(syntax.specifier && syntax.specifier->kind == SyntaxKind::RangeDimensionSpecifier);
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
                                 const ASTContext& context, const Type* typedefTarget) {
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
        if (cb->isError())
            return *cb;

        // Error if the named type is invalid for an enum base type. Other invalid types
        // will have been diagnosed already by the parser.
        if (!cb->isSimpleBitVector() && syntax.baseType->kind == SyntaxKind::NamedType) {
            context.addDiag(diag::InvalidEnumBase, syntax.baseType->getFirstToken().location())
                << *base;
            return compilation.getErrorType();
        }

        bitWidth = cb->getBitWidth();
        SLANG_ASSERT(bitWidth);
    }

    SVInt allOnes(bitWidth, 0, cb->isSigned());
    allOnes.setAllOnes();

    SVInt one(bitWidth, 1, cb->isSigned());
    ConstantValue previous;
    SourceRange previousRange;
    bool first = true;

    auto resultType = compilation.emplace<EnumType>(compilation, syntax.keyword.location(), *base,
                                                    context);
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

        if (!previous)
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
        else if (!previous) {
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

            auto dim = context.evalUnpackedDimension(*member->dimensions[0]);
            if (!dim.isRange())
                return compilation.getErrorType();

            // Range must be positive.
            if (!context.requirePositive(std::optional(dim.range.left),
                                         member->dimensions[0]->sourceRange()) ||
                !context.requirePositive(std::optional(dim.range.right),
                                         member->dimensions[0]->sourceRange())) {
                return compilation.getErrorType();
            }

            // Enum ranges must be integer literals.
            checkEnumRange(context, *member->dimensions[0]);

            // Set up the first element using the initializer. All other elements (if there are any)
            // don't get the initializer.
            int32_t index = dim.range.left;
            {
                auto& ev = EnumValueSymbol::fromSyntax(compilation, *member, *resultType, index);
                resultType->addMember(ev);

                if (member->initializer)
                    setInitializer(ev, *member->initializer);
                else
                    inferValue(ev, member->sourceRange());
            }

            bool down = dim.range.isLittleEndian();
            while (index != dim.range.right) {
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

static std::string_view getEnumValueName(Compilation& comp, std::string_view name, int32_t index) {
    if (!name.empty()) {
        SLANG_ASSERT(index >= 0);

        size_t sz = (size_t)snprintf(nullptr, 0, "%d", index);
        char* mem = (char*)comp.allocate(sz + name.size() + 1, 1);
        memcpy(mem, name.data(), name.size());
        snprintf(mem + name.size(), sz + 1, "%d", index);

        name = std::string_view(mem, sz + name.size());
    }
    return name;
}

void EnumType::createDefaultMembers(const ASTContext& context, const EnumTypeSyntax& syntax,
                                    SmallVectorBase<const Symbol*>& members) {
    auto& comp = context.getCompilation();
    for (auto member : syntax.members) {
        std::string_view name = member->name.valueText();
        SourceLocation loc = member->name.location();

        if (member->dimensions.empty()) {
            auto ev = comp.emplace<EnumValueSymbol>(name, loc);
            ev->setType(comp.getErrorType());
            members.push_back(ev);
        }
        else {
            auto dimList = member->dimensions[0];
            auto dim = context.evalUnpackedDimension(*dimList);
            if (!dim.isRange())
                continue;

            SourceRange dimRange = dimList->sourceRange();
            if (!context.requirePositive(std::optional(dim.range.left), dimRange) ||
                !context.requirePositive(std::optional(dim.range.right), dimRange)) {
                continue;
            }

            int32_t low = dim.range.lower();
            for (uint32_t i = 0; i < dim.range.width(); i++) {
                int32_t index = int32_t(i) + low;
                auto ev = comp.emplace<EnumValueSymbol>(getEnumValueName(comp, name, index), loc);
                ev->setType(comp.getErrorType());
                members.push_back(ev);
            }
        }
    }
}

EnumValueSymbol::EnumValueSymbol(std::string_view name, SourceLocation loc) :
    ValueSymbol(SymbolKind::EnumValue, name, loc, DeclaredTypeFlags::InitializerCantSeeParent) {
}

EnumValueSymbol& EnumValueSymbol::fromSyntax(Compilation& compilation,
                                             const DeclaratorSyntax& syntax, const Type& type,
                                             std::optional<int32_t> index) {
    std::string_view name = syntax.name.valueText();
    if (index)
        name = getEnumValueName(compilation, name, *index);

    auto ev = compilation.emplace<EnumValueSymbol>(name, syntax.name.location());
    ev->setType(type);
    ev->setSyntax(syntax);
    return *ev;
}

const ConstantValue& EnumValueSymbol::getValue(SourceRange referencingRange) const {
    if (!value) {
        // If no value has been explicitly set, try to set it
        // from our initializer.
        auto init = getInitializer();
        if (init) {
            auto scope = getParentScope();
            SLANG_ASSERT(scope);

            ASTContext ctx(*scope, LookupLocation::max);

            if (evaluating) {
                SLANG_ASSERT(referencingRange.start());

                auto& diag = ctx.addDiag(diag::ConstEvalParamCycle, location) << name;
                diag.addNote(diag::NoteReferencedHere, referencingRange) << referencingRange;
                return ConstantValue::Invalid;
            }

            evaluating = true;
            auto guard = ScopeGuard([this] { evaluating = false; });

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
    SLANG_ASSERT(scope);
    value = scope->getCompilation().allocConstant(std::move(newValue));
}

void EnumValueSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("value", getValue());
}

PackedArrayType::PackedArrayType(const Type& elementType, ConstantRange range,
                                 bitwidth_t fullWidth) :
    IntegralType(SymbolKind::PackedArrayType, "", SourceLocation(), fullWidth,
                 elementType.isSigned(), elementType.isFourState()),
    elementType(elementType), range(range) {
}

const Type& PackedArrayType::fromSyntax(const Scope& scope, const Type& elementType,
                                        const EvaluatedDimension& dimension,
                                        const SyntaxNode& syntax) {
    auto& comp = scope.getCompilation();
    if (elementType.isError())
        return elementType;

    if (!elementType.isIntegral()) {
        if (elementType.getCanonicalType().kind == SymbolKind::DPIOpenArrayType)
            scope.addDiag(diag::MultiplePackedOpenArrays, syntax.sourceRange());
        else
            scope.addDiag(diag::PackedArrayNotIntegral, syntax.sourceRange()) << elementType;
        return comp.getErrorType();
    }

    if (!dimension.isRange()) {
        if (dimension.kind == DimensionKind::DPIOpenArray) {
            if (elementType.isPackedArray()) {
                scope.addDiag(diag::MultiplePackedOpenArrays, syntax.sourceRange());
                return comp.getErrorType();
            }

            auto result = comp.emplace<DPIOpenArrayType>(elementType, /* isPacked */ true);
            result->setSyntax(syntax);
            return *result;
        }
        return comp.getErrorType();
    }

    return fromDim(scope, elementType, dimension.range, syntax);
}

const Type& PackedArrayType::fromDim(const Scope& scope, const Type& elementType, ConstantRange dim,
                                     DeferredSourceRange sourceRange) {
    if (elementType.isError())
        return elementType;

    auto& comp = scope.getCompilation();
    auto width = checkedMulU32(elementType.getBitWidth(), dim.width());
    if (!width || width > (uint32_t)SVInt::MAX_BITS) {
        uint64_t fullWidth = uint64_t(elementType.getBitWidth()) * dim.width();
        scope.addDiag(diag::PackedTypeTooLarge, sourceRange.get())
            << fullWidth << (uint32_t)SVInt::MAX_BITS;
        return comp.getErrorType();
    }

    auto result = comp.emplace<PackedArrayType>(elementType, dim, bitwidth_t(*width));
    if (auto syntax = sourceRange.syntax())
        result->setSyntax(*syntax);

    return *result;
}

FixedSizeUnpackedArrayType::FixedSizeUnpackedArrayType(const Type& elementType, ConstantRange range,
                                                       uint32_t selectableWidth) :
    Type(SymbolKind::FixedSizeUnpackedArrayType, "", SourceLocation()),
    elementType(elementType), range(range), selectableWidth(selectableWidth) {
}

const Type& FixedSizeUnpackedArrayType::fromDims(const Scope& scope, const Type& elementType,
                                                 std::span<const ConstantRange> dimensions,
                                                 DeferredSourceRange sourceRange) {
    const Type* result = &elementType;
    size_t count = dimensions.size();
    for (size_t i = 0; i < count; i++)
        result = &fromDim(scope, *result, dimensions[count - i - 1], sourceRange);

    return *result;
}

const Type& FixedSizeUnpackedArrayType::fromDim(const Scope& scope, const Type& elementType,
                                                ConstantRange dim,
                                                DeferredSourceRange sourceRange) {
    if (elementType.isError())
        return elementType;

    auto& comp = scope.getCompilation();
    auto width = checkedMulU32(elementType.getSelectableWidth(), dim.width());
    const uint32_t maxWidth = uint32_t(INT32_MAX) + 1;
    if (!width || width > maxWidth) {
        uint64_t fullWidth = uint64_t(elementType.getSelectableWidth()) * dim.width();
        scope.addDiag(diag::ObjectTooLarge, sourceRange.get()) << fullWidth << maxWidth;
        return comp.getErrorType();
    }

    auto result = comp.emplace<FixedSizeUnpackedArrayType>(elementType, dim, *width);
    if (auto syntax = sourceRange.syntax())
        result->setSyntax(*syntax);

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

DPIOpenArrayType::DPIOpenArrayType(const Type& elementType, bool isPacked) :
    Type(SymbolKind::DPIOpenArrayType, "", SourceLocation()), elementType(elementType),
    isPacked(isPacked) {
}

ConstantValue DPIOpenArrayType::getDefaultValueImpl() const {
    return nullptr;
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

PackedStructType::PackedStructType(Compilation& compilation, bool isSigned, SourceLocation loc,
                                   const ASTContext& context) :
    IntegralType(SymbolKind::PackedStructType, "", loc, 0, isSigned, false),
    Scope(compilation, this), systemId(compilation.getNextStructSystemId()) {

    // Struct types don't live as members of the parent scope (they're "owned" by
    // the declaration containing them) but we hook up the parent pointer so that
    // it can participate in name lookups.
    setParent(*context.scope, context.lookupIndex);
}

const Type& PackedStructType::fromSyntax(Compilation& comp, const StructUnionTypeSyntax& syntax,
                                         const ASTContext& parentContext) {
    SLANG_ASSERT(syntax.packed);
    const bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword;
    bool issuedError = false;

    auto structType = comp.emplace<PackedStructType>(comp, isSigned, syntax.keyword.location(),
                                                     parentContext);
    structType->setSyntax(syntax);

    ASTContext context(*structType, LookupLocation::max, parentContext.flags);

    SmallVector<FieldSymbol*> members;
    for (auto member : syntax.members) {
        const Type& type = comp.getType(*member->type, context);
        structType->isFourState |= type.isFourState();
        issuedError |= type.isError();

        if (!issuedError && !type.isIntegral()) {
            issuedError = true;
            auto& diag = context.addDiag(diag::PackedMemberNotIntegral,
                                         member->type->getFirstToken().location());
            diag << type;
            diag << member->type->sourceRange();
        }

        for (auto decl : member->declarators) {
            auto field = comp.emplace<FieldSymbol>(decl->name.valueText(), decl->name.location(),
                                                   0u, (uint32_t)members.size());
            field->setType(type);
            field->setSyntax(*decl);
            field->setAttributes(*context.scope, member->attributes);
            structType->addMember(*field);
            members.push_back(field);

            // Unpacked arrays are disallowed in packed structs.
            if (const Type& dimType = comp.getType(type, decl->dimensions, context);
                dimType.isUnpackedArray() && !issuedError) {

                auto& diag = context.addDiag(diag::PackedMemberNotIntegral, decl->name.range());
                diag << dimType;
                diag << decl->dimensions.sourceRange();
                issuedError = true;
            }

            structType->bitWidth += type.getBitWidth();
            if (!issuedError && structType->bitWidth > (uint32_t)SVInt::MAX_BITS) {
                context.addDiag(diag::PackedTypeTooLarge, syntax.sourceRange())
                    << structType->bitWidth << (uint32_t)SVInt::MAX_BITS;
                return comp.getErrorType();
            }

            if (decl->initializer) {
                auto& diag = context.addDiag(diag::PackedMemberHasInitializer,
                                             decl->initializer->equals.location());
                diag << decl->initializer->expr->sourceRange();
            }
        }
    }

    if (!structType->bitWidth || issuedError)
        return comp.getErrorType();

    // We added the fields in reverse order, so compute their actual
    // offsets in the right order now.
    bitwidth_t offset = 0;
    for (auto member : std::views::reverse(members)) {
        member->bitOffset = offset;
        offset += member->getType().getBitWidth();
    }

    return createPackedDims(parentContext, structType, syntax.dimensions);
}

UnpackedStructType::UnpackedStructType(Compilation& compilation, SourceLocation loc,
                                       const ASTContext& context) :
    Type(SymbolKind::UnpackedStructType, "", loc),
    Scope(compilation, this), systemId(compilation.getNextStructSystemId()) {

    // Struct types don't live as members of the parent scope (they're "owned" by
    // the declaration containing them) but we hook up the parent pointer so that
    // it can participate in name lookups.
    setParent(*context.scope, context.lookupIndex);
}

ConstantValue UnpackedStructType::getDefaultValueImpl() const {
    std::vector<ConstantValue> elements;
    for (auto field : fields)
        elements.emplace_back(field->getType().getDefaultValue());

    return elements;
}

const Type& UnpackedStructType::fromSyntax(const ASTContext& context,
                                           const StructUnionTypeSyntax& syntax) {
    SLANG_ASSERT(!syntax.packed);

    auto& comp = context.getCompilation();
    auto result = comp.emplace<UnpackedStructType>(comp, syntax.keyword.location(), context);

    uint32_t bitOffset = 0;
    SmallVector<const FieldSymbol*> fields;
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
            auto field = comp.emplace<FieldSymbol>(decl->name.valueText(), decl->name.location(),
                                                   bitOffset, (uint32_t)fields.size());
            field->setDeclaredType(*member->type);
            field->setFromDeclarator(*decl);
            field->setAttributes(*context.scope, member->attributes);
            field->randMode = randMode;

            if (randMode != RandMode::None)
                field->getDeclaredType()->addFlags(DeclaredTypeFlags::Rand);

            result->addMember(*field);
            fields.push_back(field);

            bitOffset += field->getType().getSelectableWidth();
            const uint32_t maxWidth = uint32_t(INT32_MAX) + 1;
            if (bitOffset > maxWidth) {
                context.addDiag(diag::ObjectTooLarge, syntax.sourceRange())
                    << bitOffset << maxWidth;
                return comp.getErrorType();
            }
        }
    }

    result->selectableWidth = bitOffset;
    result->fields = fields.copy(comp);
    for (auto field : result->fields) {
        // Force resolution of the initializer right away, otherwise nothing
        // is required to force it later.
        field->getInitializer();
    }

    result->setSyntax(syntax);
    return *result;
}

PackedUnionType::PackedUnionType(Compilation& compilation, bool isSigned, bool isTagged,
                                 SourceLocation loc, const ASTContext& context) :
    IntegralType(SymbolKind::PackedUnionType, "", loc, 0, isSigned, false),
    Scope(compilation, this), systemId(compilation.getNextUnionSystemId()), isTagged(isTagged),
    tagBits(0) {

    // Union types don't live as members of the parent scope (they're "owned" by
    // the declaration containing them) but we hook up the parent pointer so that
    // it can participate in name lookups.
    setParent(*context.scope, context.lookupIndex);
}

const Type& PackedUnionType::fromSyntax(Compilation& comp, const StructUnionTypeSyntax& syntax,
                                        const ASTContext& parentContext) {
    SLANG_ASSERT(syntax.packed);
    const bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword;
    const bool isTagged = syntax.tagged.valid();
    bool issuedError = false;
    uint32_t fieldIndex = 0;

    auto unionType = comp.emplace<PackedUnionType>(comp, isSigned, isTagged,
                                                   syntax.keyword.location(), parentContext);
    unionType->setSyntax(syntax);

    ASTContext context(*unionType, LookupLocation::max, parentContext.flags);

    for (auto member : syntax.members) {
        const Type& type = comp.getType(*member->type, context);
        unionType->isFourState |= type.isFourState();
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
            auto field = comp.emplace<FieldSymbol>(name.valueText(), name.location(), 0u,
                                                   fieldIndex++);
            field->setType(type);
            field->setSyntax(*decl);
            field->setAttributes(*context.scope, member->attributes);
            unionType->addMember(*field);

            // Unpacked arrays are disallowed in packed unions.
            if (const Type& dimType = comp.getType(type, decl->dimensions, context);
                dimType.isUnpackedArray() && !issuedError) {

                auto& diag = context.addDiag(diag::PackedMemberNotIntegral, decl->name.range());
                diag << dimType;
                diag << decl->dimensions.sourceRange();
                issuedError = true;
            }

            if (!unionType->bitWidth) {
                unionType->bitWidth = type.getBitWidth();
            }
            else if (isTagged) {
                // In tagged unions the members don't all have to have the same width.
                unionType->bitWidth = std::max(unionType->bitWidth, type.getBitWidth());
            }
            else if (unionType->bitWidth != type.getBitWidth() && !issuedError &&
                     !name.valueText().empty()) {
                auto& diag = context.addDiag(diag::PackedUnionWidthMismatch, name.range());
                diag << name.valueText() << type.getBitWidth() << unionType->bitWidth;
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
    if (isTagged && fieldIndex) {
        unionType->tagBits = std::bit_width(fieldIndex - 1);
        unionType->bitWidth += unionType->tagBits;
    }

    if (!unionType->bitWidth || issuedError)
        return comp.getErrorType();

    return createPackedDims(context, unionType, syntax.dimensions);
}

UnpackedUnionType::UnpackedUnionType(Compilation& compilation, bool isTagged, SourceLocation loc,
                                     const ASTContext& context) :
    Type(SymbolKind::UnpackedUnionType, "", loc),
    Scope(compilation, this), systemId(compilation.getNextUnionSystemId()), isTagged(isTagged) {

    // Union types don't live as members of the parent scope (they're "owned" by
    // the declaration containing them) but we hook up the parent pointer so that
    // it can participate in name lookups.
    setParent(*context.scope, context.lookupIndex);
}

ConstantValue UnpackedUnionType::getDefaultValueImpl() const {
    if (fields.empty())
        return nullptr;

    SVUnion u;
    u.value = fields[0]->getType().getDefaultValue();

    // Tagged unions start out with no active member.
    if (!isTagged)
        u.activeMember = 0;

    return u;
}

const Type& UnpackedUnionType::fromSyntax(const ASTContext& context,
                                          const StructUnionTypeSyntax& syntax) {
    SLANG_ASSERT(!syntax.packed);

    auto& comp = context.getCompilation();
    bool isTagged = syntax.tagged.valid();
    auto result = comp.emplace<UnpackedUnionType>(comp, isTagged, syntax.keyword.location(),
                                                  context);

    SmallVector<const FieldSymbol*> fields;
    for (auto member : syntax.members) {
        for (auto decl : member->declarators) {
            auto field = comp.emplace<FieldSymbol>(decl->name.valueText(), decl->name.location(),
                                                   0u, (uint32_t)fields.size());
            field->setDeclaredType(*member->type);
            field->setFromDeclarator(*decl);
            field->setAttributes(*context.scope, member->attributes);
            result->addMember(*field);
            fields.push_back(field);

            result->selectableWidth = std::max(result->selectableWidth,
                                               field->getType().getSelectableWidth());
        }
    }

    result->fields = fields.copy(comp);
    for (auto field : result->fields) {
        const Type* errorType;
        auto& varType = field->getType();
        if (!varType.isValidForUnion(isTagged, &errorType)) {
            if (errorType->isVirtualInterface()) {
                context.addDiag(diag::VirtualInterfaceUnionMember, field->location);
            }
            else {
                SLANG_ASSERT(!isTagged);
                context.addDiag(diag::InvalidUnionMember, field->location) << varType;
            }
        }

        // Force resolution of the initializer right away, otherwise nothing
        // is required to force it later.
        field->getInitializer();
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

const Type& VirtualInterfaceType::fromSyntax(const ASTContext& context,
                                             const VirtualInterfaceTypeSyntax& syntax) {
    auto& comp = context.getCompilation();
    auto ifaceName = syntax.name.valueText();
    if (ifaceName.empty())
        return comp.getErrorType();

    auto definition = comp.getDefinition(ifaceName, *context.scope);
    if (!definition || definition->definitionKind != DefinitionKind::Interface) {
        if (!comp.errorIfMissingExternModule(ifaceName, *context.scope, syntax.name.range())) {
            context.addDiag(diag::UnknownInterface, syntax.name.range()) << ifaceName;
        }
        return comp.getErrorType();
    }

    auto loc = syntax.name.location();
    auto& iface = InstanceSymbol::createVirtual(context, loc, *definition, syntax.parameters);

    const ModportSymbol* modport = nullptr;
    std::string_view modportName = syntax.modport ? syntax.modport->member.valueText() : ""sv;
    if (!modportName.empty() && syntax.modport) {
        auto sym = iface.body.find(modportName);
        if (!sym || sym->kind != SymbolKind::Modport) {
            SLANG_ASSERT(syntax.modport);
            auto& diag = context.addDiag(diag::NotAModport, syntax.modport->member.range());
            diag << modportName;
            diag << definition->name;
        }
        else {
            modport = &sym->as<ModportSymbol>();
        }
    }

    return *comp.emplace<VirtualInterfaceType>(iface, modport, /* isRealIface */ false, loc);
}

ConstantValue VirtualInterfaceType::getDefaultValueImpl() const {
    return ConstantValue::NullPlaceholder{};
}

ForwardingTypedefSymbol& ForwardingTypedefSymbol::fromSyntax(
    const Scope& scope, const ForwardTypedefDeclarationSyntax& syntax) {

    ForwardTypedefCategory category;
    switch (syntax.keyword.kind) {
        case TokenKind::EnumKeyword:
            category = ForwardTypedefCategory::Enum;
            break;
        case TokenKind::StructKeyword:
            category = ForwardTypedefCategory::Struct;
            break;
        case TokenKind::UnionKeyword:
            category = ForwardTypedefCategory::Union;
            break;
        case TokenKind::ClassKeyword:
            category = ForwardTypedefCategory::Class;
            break;
        default:
            category = ForwardTypedefCategory::None;
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
    auto result = comp.emplace<ForwardingTypedefSymbol>(syntax.name.valueText(),
                                                        syntax.name.location(),
                                                        ForwardTypedefCategory::InterfaceClass);
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

void ForwardingTypedefSymbol::checkType(ForwardTypedefCategory checkCategory,
                                        Visibility checkVisibility, SourceLocation declLoc) const {
    if (category != ForwardTypedefCategory::None && checkCategory != ForwardTypedefCategory::None &&
        category != checkCategory) {
        auto& diag = getParentScope()->addDiag(diag::ForwardTypedefDoesNotMatch, location);
        switch (category) {
            case ForwardTypedefCategory::Enum:
                diag << "enum"sv;
                break;
            case ForwardTypedefCategory::Struct:
                diag << "struct"sv;
                break;
            case ForwardTypedefCategory::Union:
                diag << "union"sv;
                break;
            case ForwardTypedefCategory::Class:
                diag << "class"sv;
                break;
            case ForwardTypedefCategory::InterfaceClass:
                diag << "interface class"sv;
                break;
            default:
                SLANG_UNREACHABLE;
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

TypeAliasType::TypeAliasType(std::string_view name, SourceLocation loc) :
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
    ForwardTypedefCategory category;
    switch (ct.kind) {
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
            category = ForwardTypedefCategory::Struct;
            break;
        case SymbolKind::PackedUnionType:
        case SymbolKind::UnpackedUnionType:
            category = ForwardTypedefCategory::Union;
            break;
        case SymbolKind::EnumType:
            category = ForwardTypedefCategory::Enum;
            break;
        case SymbolKind::ClassType:
            category = ForwardTypedefCategory::Class;
            if (ct.as<ClassType>().isInterface)
                category = ForwardTypedefCategory::InterfaceClass;
            break;
        default:
            category = ForwardTypedefCategory::None;
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

} // namespace slang::ast
