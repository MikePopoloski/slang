//------------------------------------------------------------------------------
// BindContext.cpp
// Expression binding context
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/BindContext.h"

#include "slang/binding/MiscExpressions.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/symbols/AttributeSymbol.h"
#include "slang/symbols/Type.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

Compilation& BindContext::getCompilation() const {
    return scope.getCompilation();
}

void BindContext::setAttributes(const Statement& stmt,
                                span<const AttributeInstanceSyntax* const> syntax) const {
    if (syntax.empty())
        return;

    getCompilation().setAttributes(stmt,
                                   AttributeSymbol::fromSyntax(syntax, scope, lookupLocation));
}

void BindContext::setAttributes(const Expression& expr,
                                span<const AttributeInstanceSyntax* const> syntax) const {
    if (syntax.empty())
        return;

    if (flags & BindFlags::NoAttributes) {
        addDiag(diag::AttributesNotAllowed, expr.sourceRange);
        return;
    }

    getCompilation().setAttributes(expr,
                                   AttributeSymbol::fromSyntax(syntax, scope, lookupLocation));
}

Diagnostic& BindContext::addDiag(DiagCode code, SourceLocation location) const {
    return scope.addDiag(code, location);
}

Diagnostic& BindContext::addDiag(DiagCode code, SourceRange sourceRange) const {
    return scope.addDiag(code, sourceRange);
}

bool BindContext::requireIntegral(const ConstantValue& cv, SourceRange range) const {
    if (cv.bad())
        return false;

    if (!cv.isInteger()) {
        addDiag(diag::ValueMustBeIntegral, range);
        return false;
    }
    return true;
}

bool BindContext::requireNoUnknowns(const SVInt& value, SourceRange range) const {
    if (value.hasUnknown()) {
        addDiag(diag::ValueMustNotBeUnknown, range);
        return false;
    }
    return true;
}

bool BindContext::requirePositive(const SVInt& value, SourceRange range) const {
    if (value.isSigned() && value.isNegative()) {
        addDiag(diag::ValueMustBePositive, range);
        return false;
    }
    return true;
}

bool BindContext::requireGtZero(optional<int32_t> value, SourceRange range) const {
    if (!value)
        return false;

    if (*value <= 0) {
        addDiag(diag::ValueMustBePositive, range);
        return false;
    }
    return true;
}

bool BindContext::requireBooleanConvertible(const Expression& expr) const {
    if (expr.bad())
        return false;

    if (!expr.type->isBooleanConvertible()) {
        addDiag(diag::NotBooleanConvertible, expr.sourceRange) << *expr.type;
        return false;
    }
    return true;
}

bool BindContext::requireValidBitWidth(bitwidth_t width, SourceRange range) const {
    if (width > SVInt::MAX_BITS) {
        addDiag(diag::ValueExceedsMaxBitWidth, range) << (int)SVInt::MAX_BITS;
        return false;
    }
    return true;
}

ConstantValue BindContext::eval(const Expression& expr) const {
    EvalContext ctx(getCompilation(), EvalFlags::CacheResults);
    ConstantValue result = expr.eval(ctx);
    ctx.reportDiags(*this);
    return result;
}

ConstantValue BindContext::tryEval(const Expression& expr) const {
    EvalContext ctx(getCompilation(), EvalFlags::CacheResults);
    return expr.eval(ctx);
}

optional<bitwidth_t> BindContext::requireValidBitWidth(const SVInt& value,
                                                       SourceRange range) const {
    auto result = value.as<bitwidth_t>();
    if (!result)
        addDiag(diag::ValueExceedsMaxBitWidth, range) << (int)SVInt::MAX_BITS;
    else if (!requireValidBitWidth(*result, range))
        return std::nullopt;
    return result;
}

optional<int32_t> BindContext::evalInteger(const ExpressionSyntax& syntax) const {
    return evalInteger(Expression::bind(syntax, resetFlags(BindFlags::Constant)));
}

optional<int32_t> BindContext::evalInteger(const Expression& expr) const {
    ConstantValue cv = eval(expr);
    if (!requireIntegral(cv, expr.sourceRange))
        return std::nullopt;

    const SVInt& value = cv.integer();
    if (!requireNoUnknowns(value, expr.sourceRange))
        return std::nullopt;

    auto coerced = value.as<int32_t>();
    if (!coerced) {
        auto& diag = addDiag(diag::ValueOutOfRange, expr.sourceRange);
        diag << value;
        diag << INT32_MIN;
        diag << INT32_MAX;
    }
    return coerced;
}

EvaluatedDimension BindContext::evalDimension(const VariableDimensionSyntax& syntax,
                                              bool requireRange, bool isPacked) const {
    EvaluatedDimension result;
    if (!syntax.specifier) {
        result.kind = DimensionKind::Dynamic;
    }
    else {
        switch (syntax.specifier->kind) {
            case SyntaxKind::QueueDimensionSpecifier: {
                result.kind = DimensionKind::Queue;
                auto maxSizeClause =
                    syntax.specifier->as<QueueDimensionSpecifierSyntax>().maxSizeClause;
                if (maxSizeClause) {
                    auto value = evalInteger(*maxSizeClause->expr);
                    if (requireGtZero(value, maxSizeClause->expr->sourceRange()))
                        result.queueMaxSize = uint32_t(*value);
                }
                break;
            }
            case SyntaxKind::WildcardDimensionSpecifier:
                result.kind = DimensionKind::Associative;
                break;
            case SyntaxKind::RangeDimensionSpecifier:
                evalRangeDimension(*syntax.specifier->as<RangeDimensionSpecifierSyntax>().selector,
                                   isPacked, result);
                break;
            default:
                THROW_UNREACHABLE;
        }
    }

    if (requireRange && !result.isRange() && result.kind != DimensionKind::Unknown)
        addDiag(diag::DimensionRequiresConstRange, syntax.sourceRange());

    return result;
}

optional<ConstantRange> BindContext::evalPackedDimension(
    const VariableDimensionSyntax& syntax) const {
    EvaluatedDimension result = evalDimension(syntax, /* requireRange */ true, /* isPacked */ true);
    if (!result.isRange())
        return std::nullopt;

    return result.range;
}

optional<ConstantRange> BindContext::evalPackedDimension(const ElementSelectSyntax& syntax) const {
    EvaluatedDimension result;
    if (syntax.selector)
        evalRangeDimension(*syntax.selector, /* isPacked */ true, result);

    if (!syntax.selector || result.kind == DimensionKind::Associative)
        addDiag(diag::DimensionRequiresConstRange, syntax.sourceRange());

    if (!result.isRange())
        return std::nullopt;

    return result.range;
}

optional<ConstantRange> BindContext::evalUnpackedDimension(
    const VariableDimensionSyntax& syntax) const {
    EvaluatedDimension result =
        evalDimension(syntax, /* requireRange */ true, /* isPacked */ false);
    if (!result.isRange())
        return std::nullopt;

    return result.range;
}

static bool checkIndexType(const Type& type) {
    auto& ct = type.getCanonicalType();
    if (ct.isFloating())
        return false;

    if (ct.isArray())
        return checkIndexType(*ct.getArrayElementType());

    switch (ct.kind) {
        case SymbolKind::PackedStructType:
        case SymbolKind::PackedUnionType:
        case SymbolKind::UnpackedStructType:
        case SymbolKind::UnpackedUnionType:
            break;
        default:
            // All other types are ok.
            return true;
    }

    // Check members recursively.
    for (auto& member : ct.as<Scope>().members()) {
        if (!checkIndexType(member.as<FieldSymbol>().getType()))
            return false;
    }

    return true;
}

void BindContext::evalRangeDimension(const SelectorSyntax& syntax, bool isPacked,
                                     EvaluatedDimension& result) const {
    switch (syntax.kind) {
        case SyntaxKind::BitSelect: {
            auto& expr = Expression::bind(*syntax.as<BitSelectSyntax>().expr, *this,
                                          BindFlags::Constant | BindFlags::AllowDataType);

            // If this expression is actually a data type, this is an associative array dimension
            // instead of a normal packed / unpacked array.
            if (expr.kind == ExpressionKind::DataType) {
                result.kind = DimensionKind::Associative;
                result.associativeType = expr.as<DataTypeExpression>().type;
                switch (result.associativeType->kind) {
                    case SymbolKind::PackedStructType:
                    case SymbolKind::PackedUnionType:
                    case SymbolKind::UnpackedStructType:
                    case SymbolKind::UnpackedUnionType:
                    case SymbolKind::EnumType:
                        addDiag(diag::CannotDeclareType, expr.sourceRange);
                        return;
                    default:
                        break;
                }

                // It's invalid for the index type to be floating or having floating members.
                if (!checkIndexType(*result.associativeType))
                    addDiag(diag::InvalidAssociativeIndexType, expr.sourceRange);
            }
            else {
                auto value = evalInteger(expr);
                if (!requireGtZero(value, syntax.sourceRange()))
                    return;

                result.kind = DimensionKind::AbbreviatedRange;
                result.range = { 0, *value - 1 };
            }
            break;
        }
        case SyntaxKind::SimpleRangeSelect: {
            auto& rangeSyntax = syntax.as<RangeSelectSyntax>();
            auto left = evalInteger(*rangeSyntax.left);
            auto right = evalInteger(*rangeSyntax.right);
            if (!left || !right)
                return;

            result.kind = DimensionKind::Range;
            result.range = { *left, *right };
            break;
        }
        default:
            addDiag(diag::InvalidDimensionRange, syntax.sourceRange());
            return;
    }

    if (result.isRange()) {
        if (isPacked && result.kind == DimensionKind::AbbreviatedRange) {
            addDiag(diag::PackedDimsRequireFullRange, syntax.sourceRange());
            result.kind = DimensionKind::Unknown;
        }
        else if (result.range.width() > SVInt::MAX_BITS) {
            if (isPacked)
                addDiag(diag::PackedArrayTooLarge, syntax.sourceRange()) << (int)SVInt::MAX_BITS;
            else
                addDiag(diag::ArrayDimTooLarge, syntax.sourceRange()) << (int)SVInt::MAX_BITS;
            result.kind = DimensionKind::Unknown;
        }
    }
}

BindContext BindContext::resetFlags(bitmask<BindFlags> addedFlags) const {
    // Remove non-sticky flags, add in any extras specified by addedFlags
    BindContext result(*this);
    result.flags &= ~(BindFlags::InsideConcatenation | BindFlags::AllowDataType |
                      BindFlags::AssignmentAllowed | BindFlags::StreamingAllowed);
    result.flags |= addedFlags;
    return result;
}

} // namespace slang
