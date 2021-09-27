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
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/symbols/AttributeSymbol.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/symbols/SubroutineSymbols.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/Type.h"

namespace slang {

Compilation& BindContext::getCompilation() const {
    return scope->getCompilation();
}

bool BindContext::isPortConnection() const {
    return instance && !instance->arrayPath.empty();
}

void BindContext::setAttributes(const Statement& stmt,
                                span<const AttributeInstanceSyntax* const> syntax) const {
    if (syntax.empty())
        return;

    getCompilation().setAttributes(stmt,
                                   AttributeSymbol::fromSyntax(syntax, *scope, getLocation()));
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
                                   AttributeSymbol::fromSyntax(syntax, *scope, getLocation()));
}

Diagnostic& BindContext::addDiag(DiagCode code, SourceLocation location) const {
    auto& diag = scope->addDiag(code, location);
    if (assertionInstance)
        addAssertionBacktrace(diag);
    return diag;
}

Diagnostic& BindContext::addDiag(DiagCode code, SourceRange sourceRange) const {
    auto& diag = scope->addDiag(code, sourceRange);
    if (assertionInstance)
        addAssertionBacktrace(diag);
    return diag;
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

bool BindContext::requirePositive(optional<int32_t> value, SourceRange range) const {
    if (!value)
        return false;

    if (*value < 0) {
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

bool BindContext::requireAssignable(const VariableSymbol& var, bool isNonBlocking,
                                    SourceLocation assignLoc, SourceRange varRange) const {
    auto reportErr = [&](DiagCode code) {
        if (!assignLoc)
            assignLoc = varRange.start();

        auto& diag = addDiag(code, assignLoc);
        diag.addNote(diag::NoteDeclarationHere, var.location);
        diag << var.name << varRange;
        return false;
    };

    if (var.isConstant) {
        // If we are in a class constructor and this variable does not have an initializer,
        // it's ok to assign to it.
        const Symbol* parent = &scope->asSymbol();
        while (parent->kind == SymbolKind::StatementBlock) {
            auto parentScope = parent->getParentScope();
            ASSERT(parentScope);
            parent = &parentScope->asSymbol();
        }

        if (var.getInitializer() || parent->kind != SymbolKind::Subroutine ||
            (parent->as<SubroutineSymbol>().flags & MethodFlags::Constructor) == 0) {
            return reportErr(diag::AssignmentToConst);
        }
    }

    if (isNonBlocking && var.lifetime == VariableLifetime::Automatic &&
        var.kind != SymbolKind::ClassProperty) {
        return reportErr(diag::NonblockingAssignmentToAuto);
    }

    if (var.kind == SymbolKind::ClockVar) {
        auto& cv = var.as<ClockVarSymbol>();
        if (cv.direction == ArgumentDirection::In)
            return reportErr(diag::WriteToInputClockVar);

        if (!isNonBlocking)
            return reportErr(diag::ClockVarSyncDrive);
    }

    // TODO: modport assignability checks
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

optional<int32_t> BindContext::evalInteger(const ExpressionSyntax& syntax,
                                           bitmask<BindFlags> extraFlags) const {
    return evalInteger(Expression::bind(syntax, resetFlags(BindFlags::Constant | extraFlags)));
}

optional<int32_t> BindContext::evalInteger(const Expression& expr) const {
    if (expr.bad())
        return std::nullopt;

    if (!expr.type->isIntegral()) {
        addDiag(diag::ExprMustBeIntegral, expr.sourceRange) << *expr.type;
        return std::nullopt;
    }

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

const ExpressionSyntax* BindContext::requireSimpleExpr(
    const PropertyExprSyntax& initialExpr) const {
    return requireSimpleExpr(initialExpr, diag::InvalidArgumentExpr);
}

const ExpressionSyntax* BindContext::requireSimpleExpr(const PropertyExprSyntax& initialExpr,
                                                       DiagCode code) const {
    const SyntaxNode* expr = &initialExpr;
    if (expr->kind == SyntaxKind::SimplePropertyExpr) {
        expr = expr->as<SimplePropertyExprSyntax>().expr;
        if (expr->kind == SyntaxKind::SimpleSequenceExpr) {
            auto& simpSeq = expr->as<SimpleSequenceExprSyntax>();
            if (!simpSeq.repetition)
                return simpSeq.expr;
        }
    }

    addDiag(code, initialExpr.sourceRange());
    return nullptr;
}

RandMode BindContext::getRandMode(const Symbol& symbol) const {
    RandMode mode = symbol.getRandMode();
    if (mode != RandMode::None)
        return mode;

    if (randomizeDetails) {
        if (auto it = randomizeDetails->scopeRandVars.find(&symbol);
            it != randomizeDetails->scopeRandVars.end()) {
            return RandMode::Rand;
        }
    }

    return RandMode::None;
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
        else if (isPacked && result.range.width() > SVInt::MAX_BITS) {
            addDiag(diag::PackedArrayTooLarge, syntax.sourceRange())
                << result.range.width() << (int)SVInt::MAX_BITS;
            result.kind = DimensionKind::Unknown;
        }
        else if (!isPacked && result.range.width() > INT32_MAX) {
            addDiag(diag::ArrayDimTooLarge, syntax.sourceRange())
                << result.range.width() << INT32_MAX;
            result.kind = DimensionKind::Unknown;
        }
    }
}

BindContext BindContext::resetFlags(bitmask<BindFlags> addedFlags) const {
    // Remove non-sticky flags, add in any extras specified by addedFlags
    static constexpr bitmask<BindFlags> NonSticky =
        BindFlags::InsideConcatenation | BindFlags::AllowDataType | BindFlags::AssignmentAllowed |
        BindFlags::StreamingAllowed | BindFlags::TopLevelStatement |
        BindFlags::AllowUnboundedLiteral | BindFlags::AllowTypeReferences |
        BindFlags::AllowClockingBlock;

    BindContext result(*this);
    result.flags &= ~NonSticky;
    result.flags |= addedFlags;
    return result;
}

void BindContext::addAssertionBacktrace(Diagnostic& diag) const {
    if (!assertionInstance)
        return;

    auto& inst = *assertionInstance;
    if (inst.argExpansionLoc) {
        diag.addNote(diag::NoteExpandedHere, inst.argExpansionLoc);
    }
    else {
        ASSERT(inst.symbol);

        auto& note = diag.addNote(diag::NoteWhileExpanding, inst.instanceLoc);
        switch (inst.symbol->kind) {
            case SymbolKind::Sequence:
                note << "sequence"sv;
                break;
            case SymbolKind::Property:
                note << "property"sv;
                break;
            case SymbolKind::LetDecl:
                note << "let declaration"sv;
                break;
            default:
                THROW_UNREACHABLE;
        }
        note << inst.symbol->name;
    }

    ASSERT(inst.prevContext);
    inst.prevContext->addAssertionBacktrace(diag);
}

} // namespace slang
