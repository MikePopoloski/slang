//------------------------------------------------------------------------------
// ASTContext.cpp
// AST creation context
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/ASTContext.h"

#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/symbols/AttributeSymbol.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/diagnostics/StatementsDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace syntax;

DriverKind ASTContext::getDriverKind() const {
    if (flags.has(ASTFlags::ProceduralAssign))
        return DriverKind::Procedural;
    if (flags.has(ASTFlags::ProceduralForceRelease))
        return DriverKind::Other;
    if (flags.has(ASTFlags::NonProcedural))
        return DriverKind::Continuous;
    return DriverKind::Procedural;
}

const InstanceSymbolBase* ASTContext::getInstance() const {
    if (instanceOrProc && instanceOrProc->kind != SymbolKind::ProceduralBlock)
        return (const InstanceSymbolBase*)instanceOrProc;
    return nullptr;
}

const ProceduralBlockSymbol* ASTContext::getProceduralBlock() const {
    if (instanceOrProc && instanceOrProc->kind == SymbolKind::ProceduralBlock)
        return &instanceOrProc->as<ProceduralBlockSymbol>();
    return nullptr;
}

const SubroutineSymbol* ASTContext::getContainingSubroutine() const {
    if (instanceOrProc)
        return nullptr;

    auto curr = scope.get();
    do {
        auto& sym = curr->asSymbol();
        if (sym.kind == SymbolKind::Subroutine)
            return &sym.as<SubroutineSymbol>();
        if (sym.kind != SymbolKind::StatementBlock)
            break;

        curr = sym.getParentScope();
    } while (curr);

    return nullptr;
}

bool ASTContext::inAlwaysCombLatch() const {
    if (auto proc = getProceduralBlock()) {
        return proc->procedureKind == ProceduralBlockKind::AlwaysComb ||
               proc->procedureKind == ProceduralBlockKind::AlwaysLatch;
    }
    return false;
}

void ASTContext::setInstance(const InstanceSymbolBase& inst) {
    SLANG_ASSERT(!instanceOrProc);
    instanceOrProc = &inst;
}

void ASTContext::setProceduralBlock(const ProceduralBlockSymbol& block) {
    SLANG_ASSERT(!instanceOrProc);
    instanceOrProc = &block;
}

const Symbol* ASTContext::tryFillAssertionDetails() {
    if (assertionInstance)
        return nullptr;

    auto parentSym = &scope->asSymbol();
    while (true) {
        if (parentSym->kind == SymbolKind::InstanceBody)
            return parentSym;

        if (parentSym->kind == SymbolKind::CheckerInstanceBody) {
            auto& body = parentSym->as<CheckerInstanceBodySymbol>();
            assertionInstance = &body.assertionDetails;
            return parentSym;
        }

        auto nextScope = parentSym->getParentScope();
        if (!nextScope)
            break;

        parentSym = &nextScope->asSymbol();
    }

    return nullptr;
}

void ASTContext::setAttributes(const Statement& stmt,
                               std::span<const AttributeInstanceSyntax* const> syntax) const {
    if (syntax.empty())
        return;

    getCompilation().setAttributes(stmt,
                                   AttributeSymbol::fromSyntax(syntax, *scope, getLocation()));
}

void ASTContext::setAttributes(const Expression& expr,
                               std::span<const AttributeInstanceSyntax* const> syntax) const {
    if (syntax.empty())
        return;

    getCompilation().setAttributes(expr,
                                   AttributeSymbol::fromSyntax(syntax, *scope, getLocation()));
}

void ASTContext::addDriver(const ValueSymbol& symbol, const Expression& longestStaticPrefix,
                           bitmask<AssignFlags> assignFlags) const {
    if (flags.has(ASTFlags::NotADriver) || scope->isUninstantiated())
        return;

    symbol.addDriver(getDriverKind(), longestStaticPrefix, getContainingSymbol(), assignFlags);
}

const Symbol& ASTContext::getContainingSymbol() const {
    const Symbol* containingSym = getProceduralBlock();
    if (!containingSym)
        containingSym = getContainingSubroutine();

    if (!containingSym)
        containingSym = &scope->asSymbol();

    return *containingSym;
}

Diagnostic& ASTContext::addDiag(DiagCode code, SourceLocation location) const {
    auto& diag = scope->addDiag(code, location);
    if (assertionInstance)
        addAssertionBacktrace(diag);
    return diag;
}

Diagnostic& ASTContext::addDiag(DiagCode code, SourceRange sourceRange) const {
    auto& diag = scope->addDiag(code, sourceRange);
    if (assertionInstance)
        addAssertionBacktrace(diag);
    return diag;
}

bool ASTContext::requireIntegral(const Expression& expr) const {
    if (expr.bad())
        return false;

    if (!expr.type->isIntegral()) {
        addDiag(diag::ExprMustBeIntegral, expr.sourceRange) << *expr.type;
        return false;
    }

    return true;
}

bool ASTContext::requireIntegral(const ConstantValue& cv, SourceRange range) const {
    if (cv.bad())
        return false;

    if (!cv.isInteger()) {
        addDiag(diag::ValueMustBeIntegral, range);
        return false;
    }
    return true;
}

bool ASTContext::requireNoUnknowns(const SVInt& value, SourceRange range) const {
    if (value.hasUnknown()) {
        addDiag(diag::ValueMustNotBeUnknown, range);
        return false;
    }
    return true;
}

bool ASTContext::requirePositive(const SVInt& value, SourceRange range) const {
    if (value.isSigned() && value.isNegative()) {
        addDiag(diag::ValueMustBePositive, range);
        return false;
    }
    return true;
}

bool ASTContext::requirePositive(std::optional<int32_t> value, SourceRange range) const {
    if (!value)
        return false;

    if (*value < 0) {
        addDiag(diag::ValueMustBePositive, range);
        return false;
    }
    return true;
}

bool ASTContext::requireGtZero(std::optional<int32_t> value, SourceRange range) const {
    if (!value)
        return false;

    if (*value <= 0) {
        addDiag(diag::ValueMustBePositive, range);
        return false;
    }
    return true;
}

bool ASTContext::requireBooleanConvertible(const Expression& expr) const {
    if (expr.bad())
        return false;

    if (!expr.type->isBooleanConvertible()) {
        addDiag(diag::NotBooleanConvertible, expr.sourceRange) << *expr.type;
        return false;
    }
    else if (expr.type->isFloating()) {
        addDiag(diag::FloatBoolConv, expr.sourceRange) << *expr.type;
    }
    else if (expr.type->isIntegral() && expr.type->getBitWidth() > 1 &&
             expr.getEffectiveWidth() > 1u) {
        // Suppress the warning for cases of right shift and bitwise-AND,
        // as it's common practice to check for non-zero results like this:
        //   if (a & b) begin end
        //   if (a >> 2) begin end
        auto isMaskOrRShift = [&] {
            if (expr.kind == ExpressionKind::BinaryOp) {
                auto op = expr.as<BinaryExpression>().op;
                return op == BinaryOperator::BinaryAnd || op == BinaryOperator::LogicalShiftRight ||
                       op == BinaryOperator::ArithmeticShiftRight ||
                       op == BinaryOperator::BinaryXor || op == BinaryOperator::BinaryXnor;
            }
            return false;
        };

        if (!isMaskOrRShift())
            addDiag(diag::IntBoolConv, expr.sourceRange) << *expr.type;
    }

    return true;
}

bool ASTContext::requireValidBitWidth(bitwidth_t width, SourceRange range) const {
    if (width > SVInt::MAX_BITS) {
        addDiag(diag::ValueExceedsMaxBitWidth, range) << (int)SVInt::MAX_BITS;
        return false;
    }
    return true;
}

bool ASTContext::requireTimingAllowed(SourceRange range) const {
    if (flags.has(ASTFlags::Function | ASTFlags::Final) || inAlwaysCombLatch()) {
        addDiag(diag::TimingInFuncNotAllowed, range);
        return false;
    }
    return true;
}

ConstantValue ASTContext::eval(const Expression& expr, bitmask<EvalFlags> extraFlags) const {
    extraFlags |= EvalFlags::CacheResults;
    if (flags.has(ASTFlags::SpecifyBlock | ASTFlags::SpecparamInitializer))
        extraFlags |= EvalFlags::SpecparamsAllowed;

    EvalContext ctx(*this, extraFlags);
    ConstantValue result = expr.eval(ctx);
    ctx.reportAllDiags();
    return result;
}

ConstantValue ASTContext::tryEval(const Expression& expr) const {
    bitmask<EvalFlags> extraFlags = EvalFlags::CacheResults;
    if (flags.has(ASTFlags::SpecifyBlock | ASTFlags::SpecparamInitializer))
        extraFlags |= EvalFlags::SpecparamsAllowed;

    EvalContext ctx(*this, extraFlags);
    return expr.eval(ctx);
}

std::optional<bitwidth_t> ASTContext::requireValidBitWidth(const SVInt& value,
                                                           SourceRange range) const {
    auto result = value.as<bitwidth_t>();
    if (!result)
        addDiag(diag::ValueExceedsMaxBitWidth, range) << (int)SVInt::MAX_BITS;
    else if (!requireValidBitWidth(*result, range))
        return std::nullopt;
    return result;
}

std::optional<int32_t> ASTContext::evalInteger(const ExpressionSyntax& syntax,
                                               bitmask<ASTFlags> extraFlags) const {
    return evalInteger(Expression::bind(syntax, *this, extraFlags));
}

std::optional<int32_t> ASTContext::evalInteger(const Expression& expr,
                                               bitmask<EvalFlags> extraFlags) const {
    if (!requireIntegral(expr))
        return std::nullopt;

    ConstantValue cv = eval(expr, extraFlags);
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

EvaluatedDimension ASTContext::evalDimension(const VariableDimensionSyntax& syntax,
                                             bool requireRange, bool isPacked) const {
    EvaluatedDimension result;
    if (!syntax.specifier) {
        result.kind = flags.has(ASTFlags::DPIArg) ? DimensionKind::DPIOpenArray
                                                  : DimensionKind::Dynamic;
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
                SLANG_UNREACHABLE;
        }
    }

    if (requireRange && !result.isRange() && result.kind != DimensionKind::Unknown &&
        result.kind != DimensionKind::DPIOpenArray) {
        addDiag(diag::DimensionRequiresConstRange, syntax.sourceRange());
    }

    return result;
}

EvaluatedDimension ASTContext::evalPackedDimension(const VariableDimensionSyntax& syntax) const {
    return evalDimension(syntax, /* requireRange */ true, /* isPacked */ true);
}

EvaluatedDimension ASTContext::evalPackedDimension(const ElementSelectSyntax& syntax) const {
    EvaluatedDimension result;
    if (syntax.selector) {
        evalRangeDimension(*syntax.selector, /* isPacked */ true, result);
    }
    else if (flags.has(ASTFlags::DPIArg)) {
        result.kind = DimensionKind::DPIOpenArray;
        return result;
    }

    if (!syntax.selector || result.kind == DimensionKind::Associative)
        addDiag(diag::DimensionRequiresConstRange, syntax.sourceRange());

    return result;
}

EvaluatedDimension ASTContext::evalUnpackedDimension(const VariableDimensionSyntax& syntax) const {
    return evalDimension(syntax, /* requireRange */ true, /* isPacked */ false);
}

const ExpressionSyntax* ASTContext::requireSimpleExpr(const PropertyExprSyntax& initialExpr) const {
    return requireSimpleExpr(initialExpr, diag::InvalidArgumentExpr);
}

const ExpressionSyntax* ASTContext::requireSimpleExpr(const PropertyExprSyntax& initialExpr,
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

RandMode ASTContext::getRandMode(const Symbol& symbol) const {
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

void ASTContext::evalRangeDimension(const SelectorSyntax& syntax, bool isPacked,
                                    EvaluatedDimension& result) const {
    switch (syntax.kind) {
        case SyntaxKind::BitSelect: {
            auto& expr = Expression::bind(*syntax.as<BitSelectSyntax>().expr, *this,
                                          ASTFlags::AllowDataType);

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
                result.range = {0, *value - 1};
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
            result.range = {*left, *right};
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
        else {
            auto fullWidth = result.range.fullWidth();
            if (isPacked && fullWidth > SVInt::MAX_BITS) {
                addDiag(diag::PackedTypeTooLarge, syntax.sourceRange())
                    << fullWidth << (int)SVInt::MAX_BITS;
                result.kind = DimensionKind::Unknown;
            }
            else if (!isPacked && fullWidth > INT32_MAX) {
                addDiag(diag::ArrayDimTooLarge, syntax.sourceRange()) << fullWidth << INT32_MAX;
                result.kind = DimensionKind::Unknown;
            }
        }
    }
}

ASTContext ASTContext::resetFlags(bitmask<ASTFlags> addedFlags) const {
    // Remove non-sticky flags, add in any extras specified by addedFlags
    static constexpr bitmask<ASTFlags> NonSticky =
        ASTFlags::InsideConcatenation | ASTFlags::AllowDataType | ASTFlags::AssignmentAllowed |
        ASTFlags::StreamingAllowed | ASTFlags::TopLevelStatement | ASTFlags::AllowUnboundedLiteral |
        ASTFlags::AllowTypeReferences | ASTFlags::AllowClockingBlock | ASTFlags::NotADriver |
        ASTFlags::AssertionDefaultArg;

    ASTContext result(*this);
    result.flags &= ~NonSticky;
    result.flags |= addedFlags;
    return result;
}

void ASTContext::addAssertionBacktrace(Diagnostic& diag) const {
    if (!assertionInstance)
        return;

    auto& inst = *assertionInstance;
    if (inst.argExpansionLoc) {
        diag.addNote(diag::NoteExpandedHere, inst.argExpansionLoc);
    }
    else {
        // We ignore checkers here; they have specialized handling in Compilation.cpp.
        SLANG_ASSERT(inst.symbol);
        if (inst.symbol->kind == SymbolKind::Checker)
            return;

        if (!inst.symbol->name.empty()) {
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
                    SLANG_UNREACHABLE;
            }
            note << inst.symbol->name;
        }
    }

    if (inst.prevContext)
        inst.prevContext->addAssertionBacktrace(diag);
}

} // namespace slang::ast
