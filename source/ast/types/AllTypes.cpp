//------------------------------------------------------------------------------
// AllTypes.cpp
// All type symbol definitions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/types/AllTypes.h"

#include <fmt/format.h>

#include "slang/ast/ASTContext.h"
#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/Expression.h"
#include "slang/ast/expressions/LiteralExpressions.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/NumericDiags.h"
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
    Type(kind, name, loc), bitWidth(bitWidth_), isSigned(isSigned_), isFourState(isFourState_) {
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

const Type& EnumType::fromSyntax(Compilation& comp, const EnumTypeSyntax& syntax,
                                 const ASTContext& context,
                                 function_ref<void(const Symbol&)> insertCB) {
    const Type* base;
    const Type* cb;
    bitwidth_t bitWidth = 32;

    if (!syntax.baseType) {
        // If no explicit base type is specified we default to an int.
        base = &comp.getIntType();
        cb = base;
        bitWidth = cb->getBitWidth();
    }
    else {
        base = &comp.getType(*syntax.baseType, context);
        cb = &base->getCanonicalType();
        if (!cb->isError()) {
            // Error if the named type is invalid for an enum base type. Other invalid types
            // will have been diagnosed already by the parser.
            if (!cb->isSimpleBitVector() && syntax.baseType->kind == SyntaxKind::NamedType) {
                context.addDiag(diag::InvalidEnumBase, syntax.baseType->getFirstToken().location())
                    << *base;
                cb = &comp.getErrorType();
            }
            else {
                bitWidth = cb->getBitWidth();
                SLANG_ASSERT(bitWidth);
            }
        }
    }

    SVInt allOnes(bitWidth, 0, cb->isSigned());
    allOnes.setAllOnes();

    SVInt one(bitWidth, 1, cb->isSigned());
    ConstantValue previous;
    SourceRange previousRange;
    bool first = true;

    auto enumType = comp.emplace<EnumType>(comp, syntax.keyword.location(), *base, context);
    enumType->setSyntax(syntax);

    // If this enum is inside a typedef we want to save the name here so that
    // when printing the types of our enum values we can refer back to this.
    if (syntax.parent && syntax.parent->kind == SyntaxKind::TypedefDeclaration)
        enumType->name = syntax.parent->as<TypedefDeclarationSyntax>().name.valueText();

    auto resultType = cb->isError() ? cb : enumType;

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
        // Clear our previous state in case there's an error and we need to exit early.
        first = false;
        previous = nullptr;

        // Create the initializer expression.
        ev.setInitializerSyntax(*initializer.expr, initializer.equals.location());
        auto initExpr = ev.getInitializer();
        SLANG_ASSERT(initExpr);
        if (initExpr->bad())
            return;

        // Drill down to the original initializer before any conversions are applied.
        initExpr = &initExpr->unwrapImplicitConversions();
        previousRange = initExpr->sourceRange;

        // [6.19] says that the initializer for an enum value must be an integer expression that
        // does not truncate any bits. Furthermore, if a sized literal constant is used, it must
        // be sized exactly to the size of the enum base type.
        auto& rt = *initExpr->type;
        if (!rt.isIntegral()) {
            context.addDiag(diag::ValueMustBeIntegral, previousRange);
            return;
        }

        if (bitWidth != rt.getBitWidth() && initExpr->kind == ExpressionKind::IntegerLiteral &&
            !initExpr->as<IntegerLiteral>().isDeclaredUnsized) {
            auto& diag = context.addDiag(diag::EnumValueSizeMismatch, previousRange);
            diag << rt.getBitWidth() << bitWidth;
        }

        ev.getValue();
        if (!initExpr->constant)
            return;

        // An enumerated name with x or z assignments assigned to an enum with no explicit data type
        // or an explicit 2-state declaration shall be a syntax error.
        auto& value = initExpr->constant->integer();
        if (!base->isFourState() && value.hasUnknown()) {
            context.addDiag(diag::EnumValueUnknownBits, previousRange) << value << *base;
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
                context.addDiag(diag::EnumValueOutOfRange, previousRange) << value << *base;
                return;
            }
        }

        previous = ev.getValue();
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
            auto& ev = EnumValueSymbol::fromSyntax(comp, *member, *resultType, std::nullopt);
            enumType->addMember(ev);
            insertCB(ev);

            if (member->initializer)
                setInitializer(ev, *member->initializer);
            else
                inferValue(ev, member->sourceRange());
        }
        else {
            if (member->dimensions.size() > 1) {
                context.addDiag(diag::EnumRangeMultiDimensional, member->dimensions.sourceRange());
            }

            auto dim = context.evalUnpackedDimension(*member->dimensions[0]);
            if (!dim.isRange())
                continue;

            // Range must be positive.
            if (!context.requirePositive(std::optional(dim.range.left),
                                         member->dimensions[0]->sourceRange()) ||
                !context.requirePositive(std::optional(dim.range.right),
                                         member->dimensions[0]->sourceRange())) {
                continue;
            }

            // Enum ranges must be integer literals.
            checkEnumRange(context, *member->dimensions[0]);

            // Set up the first element using the initializer. All other elements (if there are any)
            // don't get the initializer.
            int32_t index = dim.range.left;
            {
                auto& ev = EnumValueSymbol::fromSyntax(comp, *member, *resultType, index);
                enumType->addMember(ev);
                insertCB(ev);

                if (member->initializer)
                    setInitializer(ev, *member->initializer);
                else
                    inferValue(ev, member->sourceRange());
            }

            bool down = dim.range.isLittleEndian();
            while (index != dim.range.right) {
                index = down ? index - 1 : index + 1;

                auto& ev = EnumValueSymbol::fromSyntax(comp, *member, *resultType, index);
                enumType->addMember(ev);
                insertCB(ev);

                inferValue(ev, member->sourceRange());
            }
        }
    }

    return *resultType;
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

const Type& EnumType::findDefinition(Compilation& comp, const EnumTypeSyntax& syntax,
                                     const ASTContext& context) {
    // The enum type and all of its values should have already been created and
    // added to the parent scope. We just need to find it so we can hook up our caller.
    // To do that we're going to try to look up our first member, which should have
    // the right type. If we don't find it we know an error must have occurred during
    // type creation.
    std::string_view name;
    if (!syntax.members.empty()) {
        auto member = *syntax.members.begin();
        if (member->dimensions.empty())
            name = member->name.valueText();
        else {
            auto dimList = member->dimensions[0];
            auto dim = context.evalUnpackedDimension(*dimList);
            if (dim.isRange()) {
                SourceRange dimRange = dimList->sourceRange();
                if (context.requirePositive(std::optional(dim.range.left), dimRange) &&
                    context.requirePositive(std::optional(dim.range.right), dimRange)) {
                    name = getEnumValueName(comp, member->name.valueText(), dim.range.lower());
                }
            }
        }
    }

    auto symbol = context.scope->find(name);
    if (symbol && symbol->kind == SymbolKind::EnumValue) {
        auto& type = symbol->as<EnumValueSymbol>().getType().getCanonicalType();
        if (type.getSyntax() == &syntax)
            return createPackedDims(context, &type, syntax.dimensions);
    }

    return comp.getErrorType();
}

void EnumType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("baseType", baseType);
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

            // We set UnevaluatedBranch here so that we don't get any implicit
            // conversion warnings, since we check those manually in the enum
            // value creation path.
            ASTContext ctx(*scope, LookupLocation::max, ASTFlags::UnevaluatedBranch);

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

void PackedArrayType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("elementType", elementType);
    serializer.write("range", fmt::format("[{}:{}]", range.left, range.right));
}

FixedSizeUnpackedArrayType::FixedSizeUnpackedArrayType(const Type& elementType, ConstantRange range,
                                                       uint64_t selectableWidth,
                                                       uint64_t bitstreamWidth) :
    Type(SymbolKind::FixedSizeUnpackedArrayType, "", SourceLocation()), elementType(elementType),
    range(range), selectableWidth(selectableWidth), bitstreamWidth(bitstreamWidth) {
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
    auto selectableWidth = checkedMulU64(elementType.getSelectableWidth(), dim.width());
    auto bitstreamWidth = checkedMulU64(elementType.getBitstreamWidth(), dim.width());

    if (!selectableWidth || selectableWidth > MaxBitWidth || !bitstreamWidth ||
        bitstreamWidth > MaxBitWidth) {
        scope.addDiag(diag::ObjectTooLarge, sourceRange.get());
        return comp.getErrorType();
    }

    auto result = comp.emplace<FixedSizeUnpackedArrayType>(elementType, dim, *selectableWidth,
                                                           *bitstreamWidth);
    if (auto syntax = sourceRange.syntax())
        result->setSyntax(*syntax);

    return *result;
}

ConstantValue FixedSizeUnpackedArrayType::getDefaultValueImpl() const {
    return std::vector<ConstantValue>(range.width(), elementType.getDefaultValue());
}

void FixedSizeUnpackedArrayType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("elementType", elementType);
    serializer.write("range", fmt::format("[{}:{}]", range.left, range.right));
}

DynamicArrayType::DynamicArrayType(const Type& elementType) :
    Type(SymbolKind::DynamicArrayType, "", SourceLocation()), elementType(elementType) {
}

ConstantValue DynamicArrayType::getDefaultValueImpl() const {
    return std::vector<ConstantValue>();
}

void DynamicArrayType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("elementType", elementType);
}

DPIOpenArrayType::DPIOpenArrayType(const Type& elementType, bool isPacked) :
    Type(SymbolKind::DPIOpenArrayType, "", SourceLocation()), elementType(elementType),
    isPacked(isPacked) {
}

ConstantValue DPIOpenArrayType::getDefaultValueImpl() const {
    return nullptr;
}

void DPIOpenArrayType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("elementType", elementType);
    serializer.write("isPacked", isPacked);
}

AssociativeArrayType::AssociativeArrayType(const Type& elementType, const Type* indexType) :
    Type(SymbolKind::AssociativeArrayType, "", SourceLocation()), elementType(elementType),
    indexType(indexType) {
}

ConstantValue AssociativeArrayType::getDefaultValueImpl() const {
    return AssociativeArray();
}

void AssociativeArrayType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("elementType", elementType);
    if (indexType)
        serializer.write("indexType", *indexType);
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

void QueueType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("elementType", elementType);
    serializer.write("maxBound", maxBound);
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
        if (member->previewNode)
            structType->addMembers(*member->previewNode);

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
    Type(SymbolKind::UnpackedStructType, "", loc), Scope(compilation, this),
    systemId(compilation.getNextStructSystemId()) {

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

    uint64_t bitOffset = 0;
    uint64_t bitstreamWidth = 0;
    SmallVector<const FieldSymbol*> fields;
    for (auto member : syntax.members) {
        if (member->previewNode)
            result->addMembers(*member->previewNode);

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
            bitstreamWidth += field->getType().getBitstreamWidth();
            if (bitOffset > MaxBitWidth || bitstreamWidth > MaxBitWidth) {
                context.addDiag(diag::ObjectTooLarge, syntax.sourceRange());
                return comp.getErrorType();
            }
        }
    }

    result->selectableWidth = bitOffset;
    result->bitstreamWidth = bitstreamWidth;
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
                                 bool isSoft, SourceLocation loc, const ASTContext& context) :
    IntegralType(SymbolKind::PackedUnionType, "", loc, 0, isSigned, false),
    Scope(compilation, this), systemId(compilation.getNextUnionSystemId()), isTagged(isTagged),
    isSoft(isSoft), tagBits(0) {

    // Union types don't live as members of the parent scope (they're "owned" by
    // the declaration containing them) but we hook up the parent pointer so that
    // it can participate in name lookups.
    setParent(*context.scope, context.lookupIndex);
}

const Type& PackedUnionType::fromSyntax(Compilation& comp, const StructUnionTypeSyntax& syntax,
                                        const ASTContext& parentContext) {
    const bool isSigned = syntax.signing.kind == TokenKind::SignedKeyword;
    const bool isTagged = syntax.taggedOrSoft.kind == TokenKind::TaggedKeyword;
    const bool isSoft = syntax.taggedOrSoft.kind == TokenKind::SoftKeyword;
    bool issuedError = false;
    uint32_t fieldIndex = 0;

    auto unionType = comp.emplace<PackedUnionType>(comp, isSigned, isTagged, isSoft,
                                                   syntax.keyword.location(), parentContext);
    unionType->setSyntax(syntax);

    ASTContext context(*unionType, LookupLocation::max, parentContext.flags);

    for (auto member : syntax.members) {
        if (member->previewNode)
            unionType->addMembers(*member->previewNode);

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
            else if (isTagged || isSoft) {
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
        unionType->tagBits = (uint32_t)std::bit_width(fieldIndex - 1);
        unionType->bitWidth += unionType->tagBits;
    }

    if (!unionType->bitWidth || issuedError)
        return comp.getErrorType();

    return createPackedDims(context, unionType, syntax.dimensions);
}

void PackedUnionType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("isTagged", isTagged);
    serializer.write("isSoft", isSoft);
}

UnpackedUnionType::UnpackedUnionType(Compilation& compilation, bool isTagged, SourceLocation loc,
                                     const ASTContext& context) :
    Type(SymbolKind::UnpackedUnionType, "", loc), Scope(compilation, this),
    systemId(compilation.getNextUnionSystemId()), isTagged(isTagged) {

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
    bool isTagged = syntax.taggedOrSoft.kind == TokenKind::TaggedKeyword;
    auto result = comp.emplace<UnpackedUnionType>(comp, isTagged, syntax.keyword.location(),
                                                  context);

    SmallVector<const FieldSymbol*> fields;
    for (auto member : syntax.members) {
        if (member->previewNode)
            result->addMembers(*member->previewNode);

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
            result->bitstreamWidth = std::max(result->bitstreamWidth,
                                              field->getType().getBitstreamWidth());
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

void UnpackedUnionType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("isTagged", isTagged);
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

    auto def = comp.getDefinition(ifaceName, *context.scope, syntax.name.range(),
                                  diag::UnknownInterface)
                   .definition;

    if (!def || def->kind != SymbolKind::Definition ||
        def->as<DefinitionSymbol>().definitionKind != DefinitionKind::Interface) {

        // If we got a result from getDefinition then it didn't error, so issue
        // one ourselves since we didn't find an interface.
        if (def)
            context.addDiag(diag::UnknownInterface, syntax.name.range()) << ifaceName;
        return comp.getErrorType();
    }

    auto loc = syntax.name.location();
    auto& iface = InstanceSymbol::createVirtual(context, loc, def->as<DefinitionSymbol>(),
                                                syntax.parameters);
    comp.noteVirtualIfaceInstance(iface);

    const ModportSymbol* modport = nullptr;
    std::string_view modportName = syntax.modport ? syntax.modport->member.valueText() : ""sv;
    if (!modportName.empty() && syntax.modport) {
        auto sym = iface.body.find(modportName);
        if (!sym || sym->kind != SymbolKind::Modport) {
            SLANG_ASSERT(syntax.modport);
            auto& diag = context.addDiag(diag::NotAModport, syntax.modport->member.range());
            diag << modportName;
            diag << def->name;
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

void VirtualInterfaceType::serializeTo(ASTSerializer& serializer) const {
    serializer.write("target", toString());
}

ForwardingTypedefSymbol& ForwardingTypedefSymbol::fromSyntax(
    const Scope& scope, const ForwardTypedefDeclarationSyntax& syntax) {

    auto typeRestriction = ForwardTypeRestriction::None;
    if (syntax.typeRestriction)
        typeRestriction = SemanticFacts::getTypeRestriction(*syntax.typeRestriction);

    auto& comp = scope.getCompilation();
    auto result = comp.emplace<ForwardingTypedefSymbol>(syntax.name.valueText(),
                                                        syntax.name.location(), typeRestriction);
    result->setSyntax(syntax);
    result->setAttributes(scope, syntax.attributes);
    return *result;
}

ForwardingTypedefSymbol& ForwardingTypedefSymbol::fromSyntax(
    const Scope& scope, const ClassPropertyDeclarationSyntax& syntax) {

    auto& result = fromSyntax(scope, syntax.declaration->as<ForwardTypedefDeclarationSyntax>());
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

void ForwardingTypedefSymbol::addForwardDecl(const ForwardingTypedefSymbol& decl) const {
    if (!next)
        next = &decl;
    else
        next->addForwardDecl(decl);
}

void ForwardingTypedefSymbol::checkType(ForwardTypeRestriction checkRestriction,
                                        Visibility checkVisibility, SourceLocation declLoc) const {
    if (typeRestriction != ForwardTypeRestriction::None && typeRestriction != checkRestriction) {
        auto& diag = getParentScope()->addDiag(diag::ForwardTypedefDoesNotMatch, location);
        diag << SemanticFacts::getTypeRestrictionText(typeRestriction);
        diag.addNote(diag::NoteDeclarationHere, declLoc);
        return;
    }

    if (visibility && visibility != checkVisibility) {
        auto& diag = getParentScope()->addDiag(diag::ForwardTypedefVisibility, location);
        diag.addNote(diag::NoteDeclarationHere, declLoc);
        return;
    }

    if (next)
        next->checkType(checkRestriction, checkVisibility, declLoc);
}

void ForwardingTypedefSymbol::serializeTo(ASTSerializer& serializer) const {
    serializer.write("category", toString(typeRestriction));
    if (next)
        serializer.write("next", *next);
}

TypeAliasType::TypeAliasType(std::string_view name, SourceLocation loc) :
    Type(SymbolKind::TypeAlias, name, loc), targetType(*this, DeclaredTypeFlags::TypedefTarget) {
    canonical = nullptr;
}

TypeAliasType& TypeAliasType::fromSyntax(const Scope& scope,
                                         const TypedefDeclarationSyntax& syntax) {
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
    if (firstForward) {
        firstForward->checkType(SemanticFacts::getTypeRestriction(targetType.getType()), visibility,
                                location);
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

} // namespace slang::ast
