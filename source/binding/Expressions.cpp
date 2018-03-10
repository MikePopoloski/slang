//------------------------------------------------------------------------------
// Expressions.cpp
// Expression creation and analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "Expressions.h"

#include "compilation/Compilation.h"
#include "symbols/TypeSymbols.h"

namespace {

using namespace slang;

const Type* binaryOperatorType(Compilation& compilation, const Type* lt, const Type* rt, bool forceFourState) {
    // Figure out what the result type of an arithmetic binary operator should be. The rules are:
    // - If either operand is real, the result is real
    // - Otherwise, if either operand is shortreal, the result is shortreal
    // - Otherwise, result is integral with the following properties:
    //      - Bit width is max(lhs, rhs)
    //      - If either operand is four state (or if we force it), the result is four state
    //      - If either operand is unsigned, the result is unsigned
    const Type* result;
    if (lt->isFloating() || rt->isFloating()) {
        if ((lt->isFloating() && lt->getBitWidth() == 64) ||
            (rt->isFloating() && rt->getBitWidth() == 64)) {
            result = &compilation.getRealType();
        }
        else {
            result = &compilation.getShortRealType();
        }
    }
    else {
        bitwidth_t width = std::max(lt->getBitWidth(), rt->getBitWidth());

        bitmask<IntegralFlags> lf = lt->getIntegralFlags();
        bitmask<IntegralFlags> rf = rt->getIntegralFlags();

        bitmask<IntegralFlags> flags;
        if ((lf & IntegralFlags::Signed) && (rf & IntegralFlags::Signed))
            flags |= IntegralFlags::Signed;
        if (forceFourState || (lf & IntegralFlags::FourState) || (rf & IntegralFlags::FourState))
            flags |= IntegralFlags::FourState;
        if ((lf & IntegralFlags::Reg) && (rf & IntegralFlags::Reg))
            flags |= IntegralFlags::Reg;

        // If the width is 1, try to preserve whether this was a packed array with a width of 1
        // or a plain scalar type with no dimensions specified.
        if (width == 1 && (lt->isScalar() || rt->isScalar()))
            result = &compilation.getScalarType(flags);
        else
            result = &compilation.getType(width, flags);
    }

    // Attempt to preserve any type aliases passed in when selecting the result.
    if (lt->isMatching(*result))
        return lt;
    if (rt->isMatching(*result))
        return rt;
    return result;
}

const Type* forceFourState(Compilation& compilation, const Type* type) {
    if (type->isFloating() || type->isFourState())
        return type;

    // Use the logic in binaryOperatorType to create a type with the correct size and sign.
    return binaryOperatorType(compilation, type, type, true);
}

const Type* singleBitType(Compilation& compilation, const Type* lt, const Type* rt) {
    if (lt->isFourState() || rt->isFourState())
        return &compilation.getLogicType();
    return &compilation.getBitType();
}

}

namespace slang {

const InvalidExpression InvalidExpression::Instance(nullptr, ErrorType::Instance);

const Expression& Expression::bind(Compilation& compilation, const ExpressionSyntax& syntax,
                                   const BindContext& context) {
    return selfDetermined(compilation, syntax, context);
}

const Expression& Expression::bind(Compilation& compilation, const Type& lhs, const ExpressionSyntax& rhs,
                                   SourceLocation location, const BindContext& context) {
    Expression& expr = create(compilation, rhs, context);
    if (expr.bad() || lhs.isError())
        return expr;

    const Type* type = expr.type;
    if (!lhs.isAssignmentCompatible(*type)) {
        DiagCode code = lhs.isCastCompatible(*type) ? DiagCode::NoImplicitConversion : DiagCode::BadAssignment;
        compilation.addError(code, location) << rhs.sourceRange();
        return *compilation.emplace<InvalidExpression>(&expr, compilation.getErrorType());
    }

    if (lhs.getBitWidth() > type->getBitWidth()) {
        if (!lhs.isFloating() && !type->isFloating())
            type = &compilation.getType(lhs.getBitWidth(), type->getIntegralFlags());
        else {
            if (lhs.getBitWidth() > 32)
                type = &compilation.getRealType();
            else
                type = &compilation.getShortRealType();
        }
    }
    else {
        // TODO: truncation
    }

    Expression* e = &expr;
    Expression::contextDetermined(compilation, e, *type);
    return *e;
}

bool Expression::bad() const {
    return kind == ExpressionKind::Invalid || type->isError();
}

bool Expression::isLValue() const {
    switch (kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::ElementSelect:
        case ExpressionKind::RangeSelect:
        case ExpressionKind::MemberAccess:
            return true;
        default:
            return false;
    }
}

Expression& Expression::create(Compilation& compilation, const ExpressionSyntax& syntax, const BindContext& context) {
    switch (syntax.kind) {
        case SyntaxKind::NullLiteralExpression:
            return NullLiteral::fromSyntax(compilation, syntax.as<LiteralExpressionSyntax>());
        case SyntaxKind::StringLiteralExpression:
            return StringLiteral::fromSyntax(compilation, syntax.as<LiteralExpressionSyntax>());
        case SyntaxKind::TimeLiteralExpression:
        case SyntaxKind::WildcardLiteralExpression:
        case SyntaxKind::OneStepLiteralExpression:
            // TODO: unimplemented
            break;
        case SyntaxKind::IdentifierName:
        case SyntaxKind::IdentifierSelectName:
        case SyntaxKind::ScopedName:
            return bindName(compilation, syntax.as<NameSyntax>(), context);
        case SyntaxKind::RealLiteralExpression:
            return RealLiteral::fromSyntax(compilation, syntax.as<LiteralExpressionSyntax>());
        case SyntaxKind::IntegerLiteralExpression:
            return IntegerLiteral::fromSyntax(compilation, syntax.as<LiteralExpressionSyntax>());
        case SyntaxKind::UnbasedUnsizedLiteralExpression:
            return UnbasedUnsizedIntegerLiteral::fromSyntax(compilation, syntax.as<LiteralExpressionSyntax>());
        case SyntaxKind::IntegerVectorExpression:
            return IntegerLiteral::fromSyntax(compilation, syntax.as<IntegerVectorExpressionSyntax>());
        case SyntaxKind::ParenthesizedExpression:
            return create(compilation, syntax.as<ParenthesizedExpressionSyntax>().expression, context);
        case SyntaxKind::UnaryPlusExpression:
        case SyntaxKind::UnaryMinusExpression:
        case SyntaxKind::UnaryBitwiseNotExpression:
        case SyntaxKind::UnaryBitwiseAndExpression:
        case SyntaxKind::UnaryBitwiseOrExpression:
        case SyntaxKind::UnaryBitwiseXorExpression:
        case SyntaxKind::UnaryBitwiseNandExpression:
        case SyntaxKind::UnaryBitwiseNorExpression:
        case SyntaxKind::UnaryBitwiseXnorExpression:
        case SyntaxKind::UnaryLogicalNotExpression:
        case SyntaxKind::UnaryPreincrementExpression:
        case SyntaxKind::UnaryPredecrementExpression:
            return UnaryExpression::fromSyntax(compilation, syntax.as<PrefixUnaryExpressionSyntax>(), context);
        case SyntaxKind::PostincrementExpression:
        case SyntaxKind::PostdecrementExpression:
            return UnaryExpression::fromSyntax(compilation, syntax.as<PostfixUnaryExpressionSyntax>(), context);
        case SyntaxKind::AddExpression:
        case SyntaxKind::SubtractExpression:
        case SyntaxKind::MultiplyExpression:
        case SyntaxKind::DivideExpression:
        case SyntaxKind::ModExpression:
        case SyntaxKind::BinaryAndExpression:
        case SyntaxKind::BinaryOrExpression:
        case SyntaxKind::BinaryXorExpression:
        case SyntaxKind::BinaryXnorExpression:
        case SyntaxKind::EqualityExpression:
        case SyntaxKind::InequalityExpression:
        case SyntaxKind::CaseEqualityExpression:
        case SyntaxKind::CaseInequalityExpression:
        case SyntaxKind::GreaterThanEqualExpression:
        case SyntaxKind::GreaterThanExpression:
        case SyntaxKind::LessThanEqualExpression:
        case SyntaxKind::LessThanExpression:
        case SyntaxKind::WildcardEqualityExpression:
        case SyntaxKind::WildcardInequalityExpression:
        case SyntaxKind::LogicalAndExpression:
        case SyntaxKind::LogicalOrExpression:
        case SyntaxKind::LogicalImplicationExpression:
        case SyntaxKind::LogicalEquivalenceExpression:
        case SyntaxKind::LogicalShiftLeftExpression:
        case SyntaxKind::LogicalShiftRightExpression:
        case SyntaxKind::ArithmeticShiftLeftExpression:
        case SyntaxKind::ArithmeticShiftRightExpression:
        case SyntaxKind::PowerExpression:
        case SyntaxKind::AssignmentExpression:
        case SyntaxKind::AddAssignmentExpression:
        case SyntaxKind::SubtractAssignmentExpression:
        case SyntaxKind::MultiplyAssignmentExpression:
        case SyntaxKind::DivideAssignmentExpression:
        case SyntaxKind::ModAssignmentExpression:
        case SyntaxKind::AndAssignmentExpression:
        case SyntaxKind::OrAssignmentExpression:
        case SyntaxKind::XorAssignmentExpression:
        case SyntaxKind::LogicalLeftShiftAssignmentExpression:
        case SyntaxKind::LogicalRightShiftAssignmentExpression:
        case SyntaxKind::ArithmeticLeftShiftAssignmentExpression:
        case SyntaxKind::ArithmeticRightShiftAssignmentExpression:
            return BinaryExpression::fromSyntax(compilation, syntax.as<BinaryExpressionSyntax>(), context);
        case SyntaxKind::InvocationExpression:
            return CallExpression::fromSyntax(compilation, syntax.as<InvocationExpressionSyntax>(), context);
        case SyntaxKind::ConditionalExpression:
            return ConditionalExpression::fromSyntax(compilation, syntax.as<ConditionalExpressionSyntax>(), context);
        case SyntaxKind::ConcatenationExpression:
            return ConcatenationExpression::fromSyntax(compilation, syntax.as<ConcatenationExpressionSyntax>(),
                                                       context);
        case SyntaxKind::MultipleConcatenationExpression:
            return ReplicationExpression::fromSyntax(compilation, syntax.as<MultipleConcatenationExpressionSyntax>(),
                                                     context);
        case SyntaxKind::ElementSelectExpression:
            return bindSelectExpression(compilation, syntax.as<ElementSelectExpressionSyntax>(), context);
        default:
            THROW_UNREACHABLE;
    }
    return badExpr(compilation, nullptr);
}

Expression& Expression::bindName(Compilation& compilation, const NameSyntax& syntax, const BindContext& context) {
    LookupResult result;
    context.scope.lookupName(syntax, context.lookupLocation, context.lookupKind, result);

    if (result.hasError())
        compilation.addDiagnostics(result.diagnostics);

    const Symbol* symbol = result.found;
    if (!symbol)
        return badExpr(compilation, nullptr);

    if (!symbol->isValue()) {
        compilation.addError(DiagCode::NotAType, syntax.sourceRange()) << symbol->name;
        return badExpr(compilation, nullptr);
    }

    Expression* expr = compilation.emplace<NamedValueExpression>(symbol->as<ValueSymbol>(), syntax.sourceRange());
    
    // Drill down into member accesses.
    for (const auto& selector : result.selectors) {
        if (expr->bad())
            return *expr;

        auto memberSelect = std::get_if<LookupResult::MemberSelector>(&selector);
        if (memberSelect) {
            string_view name = memberSelect->name;
            if (name.empty())
                return badExpr(compilation, expr);

            if (!expr->type->isStructUnion()) {
                auto& diag = compilation.addError(DiagCode::MemberAccessNotStructUnion, memberSelect->dotLocation);
                diag << expr->sourceRange;
                diag << memberSelect->nameRange;
                diag << *expr->type;
                return badExpr(compilation, expr);
            }

            const Symbol* member = expr->type->getCanonicalType().as<Scope>().find(name);
            if (!member) {
                auto& diag = compilation.addError(DiagCode::UnknownMember, memberSelect->nameRange);
                diag << expr->sourceRange;
                diag << name;
                diag << *expr->type;
                return badExpr(compilation, expr);
            }

            // The source range of the entire member access starts from the value being selected.
            SourceRange range { expr->sourceRange.start(), memberSelect->nameRange.end() };
            const auto& field = member->as<FieldSymbol>();
            expr = compilation.emplace<MemberAccessExpression>(field.getType(), *expr, field, range);
        }
        else {
            // Element / range selectors.
            const ElementSelectSyntax* selectSyntax = std::get<const ElementSelectSyntax*>(selector);
            expr = &bindSelector(compilation, *expr, *selectSyntax, context);
        }
    }

    return *expr;
}

Expression& Expression::bindSelectExpression(Compilation& compilation, const ElementSelectExpressionSyntax& syntax,
                                             const BindContext& context) {
    Expression& value = create(compilation, syntax.left, context);
    return bindSelector(compilation, value, syntax.select, context);
}

Expression& Expression::bindSelector(Compilation& compilation, Expression& value, const ElementSelectSyntax& syntax,
                                     const BindContext& context) {
    // The full source range of the expression includes the value and the selector syntax.
    SourceRange fullRange = { value.sourceRange.start(), syntax.sourceRange().end() };

    // TODO: null selector?
    const SelectorSyntax* selector = syntax.selector;
    switch (selector->kind) {
        case SyntaxKind::BitSelect:
            return ElementSelectExpression::fromSyntax(compilation, value, selector->as<BitSelectSyntax>().expr,
                                                       fullRange, context);
        case SyntaxKind::SimpleRangeSelect:
        case SyntaxKind::AscendingRangeSelect:
        case SyntaxKind::DescendingRangeSelect:
            return RangeSelectExpression::fromSyntax(compilation, value, selector->as<RangeSelectSyntax>(),
                                                     fullRange, context);
        default:
            THROW_UNREACHABLE;
    }
}

Expression& Expression::convert(Compilation& compilation, ConversionKind conversionKind, const Type& type,
                                Expression& expr) {
    return *compilation.emplace<ConversionExpression>(conversionKind, type, expr, expr.sourceRange);
}

Expression& Expression::badExpr(Compilation& compilation, const Expression* expr) {
    return *compilation.emplace<InvalidExpression>(expr, compilation.getErrorType());
}

bool Expression::checkLValue(Compilation& compilation, const Expression& expr, SourceLocation location) {
    if (!expr.isLValue()) {
        auto& diag = compilation.addError(DiagCode::ExpressionNotAssignable, location);
        diag << expr.sourceRange;
        return false;
    }
    return true;
}

IntegerLiteral::IntegerLiteral(BumpAllocator& alloc, const Type& type, const SVInt& value,
                               SourceRange sourceRange) :
    Expression(ExpressionKind::IntegerLiteral, type, sourceRange),
    valueStorage(value.getBitWidth(), value.isSigned(), value.hasUnknown())
{
    if (value.isSingleWord())
        valueStorage.val = *value.getRawData();
    else {
        valueStorage.pVal = (uint64_t*)alloc.allocate(sizeof(uint64_t) * value.getNumWords(), alignof(uint64_t));
        memcpy(valueStorage.pVal, value.getRawData(), sizeof(uint64_t) * value.getNumWords());
    }
}

Expression& IntegerLiteral::fromSyntax(Compilation& compilation, const LiteralExpressionSyntax& syntax) {
    ASSERT(syntax.kind == SyntaxKind::IntegerLiteralExpression);

    return *compilation.emplace<IntegerLiteral>(
        compilation, compilation.getIntType(),
        syntax.literal.intValue(), syntax.sourceRange()
    );
}

Expression& IntegerLiteral::fromSyntax(Compilation& compilation, const IntegerVectorExpressionSyntax& syntax) {
    const SVInt& value = syntax.value.intValue();

    bitmask<IntegralFlags> flags;
    if (value.isSigned())
        flags |= IntegralFlags::Signed;
    if (value.hasUnknown())
        flags |= IntegralFlags::FourState;

    const Type& type = compilation.getType(value.getBitWidth(), flags);
    return *compilation.emplace<IntegerLiteral>(compilation, type, value, syntax.sourceRange());
}

Expression& RealLiteral::fromSyntax(Compilation& compilation, const LiteralExpressionSyntax& syntax) {
    ASSERT(syntax.kind == SyntaxKind::RealLiteralExpression);

    return *compilation.emplace<RealLiteral>(
        compilation.getRealType(), syntax.literal.realValue(),
        syntax.sourceRange()
    );
}

Expression& UnbasedUnsizedIntegerLiteral::fromSyntax(Compilation& compilation,
                                                     const LiteralExpressionSyntax& syntax) {
    ASSERT(syntax.kind == SyntaxKind::UnbasedUnsizedLiteralExpression);

    // UnsizedUnbasedLiteralExpressions default to a size of 1 in an undetermined
    // context, but can grow to be wider during propagation.
    logic_t val = syntax.literal.bitValue();
    return *compilation.emplace<UnbasedUnsizedIntegerLiteral>(
        compilation.getType(1, val.isUnknown() ? IntegralFlags::FourState : IntegralFlags::TwoState),
        val, syntax.sourceRange()
    );
}

Expression& NullLiteral::fromSyntax(Compilation& compilation, const LiteralExpressionSyntax& syntax) {
    ASSERT(syntax.kind == SyntaxKind::NullLiteralExpression);
    return *compilation.emplace<NullLiteral>(compilation.getNullType(), syntax.sourceRange());
}

Expression& StringLiteral::fromSyntax(Compilation& compilation, const LiteralExpressionSyntax& syntax) {
    ASSERT(syntax.kind == SyntaxKind::StringLiteralExpression);

    // The standard does not say what the type width should be when the literal is empty
    // (since you can't have a zero-width integer) so let's pretend there's a null byte there.
    // TODO: overflow of literal
    string_view value = syntax.literal.valueText();
    bitwidth_t width = value.empty() ? 8 : bitwidth_t(value.size()) * 8;
    const auto& type = compilation.getType(width, IntegralFlags::Unsigned);

    return *compilation.emplace<StringLiteral>(type, value, syntax.sourceRange());
}

Expression& UnaryExpression::fromSyntax(Compilation& compilation, const PrefixUnaryExpressionSyntax& syntax,
                                        const BindContext& context) {
    Expression& operand = create(compilation, syntax.operand, context);
    const Type* type = operand.type;

    Expression* result = compilation.emplace<UnaryExpression>(getUnaryOperator(syntax.kind), *type,
                                                              operand, syntax.sourceRange());
    if (operand.bad())
        return badExpr(compilation, result);

    bool good;
    switch (syntax.kind) {
        case SyntaxKind::UnaryPlusExpression:
        case SyntaxKind::UnaryMinusExpression:
            // Supported for both integral and real types. Result is same as input type.
            good = type->isNumeric();
            result->type = type;
            break;
        case SyntaxKind::UnaryLogicalNotExpression:
            // Supported for both integral and real types. Result is a single bit.
            good = type->isNumeric();
            result->type = type->isFourState() ? &compilation.getLogicType() : &compilation.getBitType();
            break;
        case SyntaxKind::UnaryBitwiseNotExpression:
        case SyntaxKind::UnaryBitwiseAndExpression:
        case SyntaxKind::UnaryBitwiseOrExpression:
        case SyntaxKind::UnaryBitwiseXorExpression:
        case SyntaxKind::UnaryBitwiseNandExpression:
        case SyntaxKind::UnaryBitwiseNorExpression:
        case SyntaxKind::UnaryBitwiseXnorExpression:
            // Supported for integral only. Result type is always a single bit.
            good = type->isIntegral();
            result->type = type->isFourState() ? &compilation.getLogicType() : &compilation.getBitType();
            break;
        case SyntaxKind::UnaryPreincrementExpression:
        case SyntaxKind::UnaryPredecrementExpression:
            // Supported for both integral and real types. Result is same as input type.
            // The operand must also be an assignable lvalue.
            good = type->isNumeric();
            result->type = type;
            if (!checkLValue(compilation, operand, syntax.operatorToken.location()))
                return badExpr(compilation, result);
            break;
        default:
            THROW_UNREACHABLE;
    }

    if (!good) {
        auto& diag = compilation.addError(DiagCode::BadUnaryExpression, syntax.operatorToken.location());
        diag << *type;
        diag << operand.sourceRange;
        return badExpr(compilation, result);
    }

    return *result;
}

Expression& UnaryExpression::fromSyntax(Compilation& compilation, const PostfixUnaryExpressionSyntax& syntax,
                                        const BindContext& context) {
    Expression& operand = create(compilation, syntax.operand, context);
    const Type* type = operand.type;

    // This method is only ever called for postincrement and postdecrement operators, so
    // the operand must be an lvalue.
    Expression* result = compilation.emplace<UnaryExpression>(getUnaryOperator(syntax.kind), *type,
                                                              operand, syntax.sourceRange());
    if (operand.bad() || !checkLValue(compilation, operand, syntax.operatorToken.location()))
        return badExpr(compilation, result);

    if (!type->isNumeric()) {
        auto& diag = compilation.addError(DiagCode::BadUnaryExpression, syntax.operatorToken.location());
        diag << *type;
        diag << operand.sourceRange;
        return badExpr(compilation, result);
    }

    return *result;
}

Expression& BinaryExpression::fromSyntax(Compilation& compilation, const BinaryExpressionSyntax& syntax,
                                         const BindContext& context) {
    Expression& lhs = create(compilation, syntax.left, context);
    Expression& rhs = create(compilation, syntax.right, context);
    const Type* lt = lhs.type;
    const Type* rt = rhs.type;

    auto result = compilation.emplace<BinaryExpression>(getBinaryOperator(syntax.kind), *lhs.type,
                                                        lhs, rhs, syntax.sourceRange());
    if (lhs.bad() || rhs.bad())
        return badExpr(compilation, result);

    bool bothIntegral = lt->isIntegral() && rt->isIntegral();
    bool bothNumeric = lt->isNumeric() && rt->isNumeric();

    bool good;
    switch (syntax.kind) {
        case SyntaxKind::AddExpression:
        case SyntaxKind::SubtractExpression:
        case SyntaxKind::MultiplyExpression:
        case SyntaxKind::AddAssignmentExpression:
        case SyntaxKind::SubtractAssignmentExpression:
        case SyntaxKind::MultiplyAssignmentExpression:
            good = bothNumeric;
            result->type = binaryOperatorType(compilation, lt, rt, false);
            break;
        case SyntaxKind::DivideExpression:
        case SyntaxKind::DivideAssignmentExpression:
            // Result is forced to 4-state because result can be X.
            good = bothNumeric;
            result->type = binaryOperatorType(compilation, lt, rt, true);
            break;
        case SyntaxKind::ModExpression:
        case SyntaxKind::ModAssignmentExpression:
            // Result is forced to 4-state because result can be X.
            // Different from divide because only integers are allowed.
            good = bothIntegral;
            result->type = binaryOperatorType(compilation, lt, rt, true);
            break;
        case SyntaxKind::BinaryAndExpression:
        case SyntaxKind::BinaryOrExpression:
        case SyntaxKind::BinaryXorExpression:
        case SyntaxKind::BinaryXnorExpression:
        case SyntaxKind::AndAssignmentExpression:
        case SyntaxKind::OrAssignmentExpression:
        case SyntaxKind::XorAssignmentExpression:
            good = bothIntegral;
            result->type = binaryOperatorType(compilation, lt, rt, false);
            break;
        case SyntaxKind::LogicalShiftLeftExpression:
        case SyntaxKind::LogicalShiftRightExpression:
        case SyntaxKind::ArithmeticShiftLeftExpression:
        case SyntaxKind::ArithmeticShiftRightExpression:
        case SyntaxKind::LogicalLeftShiftAssignmentExpression:
        case SyntaxKind::LogicalRightShiftAssignmentExpression:
        case SyntaxKind::ArithmeticLeftShiftAssignmentExpression:
        case SyntaxKind::ArithmeticRightShiftAssignmentExpression:
            // The result is always the same type as the lhs, except that if the rhs is
            // four state then the lhs also becomes four state.
            good = bothIntegral;
            if (rt->isFourState())
                result->type = forceFourState(compilation, lt);
            else
                result->type = lt;
            break;
        case SyntaxKind::PowerExpression:
            // Result is forced to 4-state because result can be X.
            good = bothNumeric;
            result->type = forceFourState(compilation, lt);
            break;
        case SyntaxKind::GreaterThanEqualExpression:
        case SyntaxKind::GreaterThanExpression:
        case SyntaxKind::LessThanEqualExpression:
        case SyntaxKind::LessThanExpression: {
            // Result is always a single bit.
            good = bothNumeric;
            result->type = singleBitType(compilation, lt, rt);

            // Result type is fixed but the two operands affect each other as they would in
            // other context-determined operators.
            auto nt = binaryOperatorType(compilation, lt, rt, false);
            contextDetermined(compilation, result->left_, *nt);
            contextDetermined(compilation, result->right_, *nt);
            break;
        }
        case SyntaxKind::LogicalAndExpression:
        case SyntaxKind::LogicalOrExpression:
        case SyntaxKind::LogicalImplicationExpression:
        case SyntaxKind::LogicalEquivalenceExpression:
            // Result is always a single bit.
            good = bothNumeric;
            result->type = singleBitType(compilation, lt, rt);
            break;
        case SyntaxKind::EqualityExpression:
        case SyntaxKind::InequalityExpression:
        case SyntaxKind::WildcardEqualityExpression:
        case SyntaxKind::WildcardInequalityExpression:
        case SyntaxKind::CaseEqualityExpression:
        case SyntaxKind::CaseInequalityExpression:
            // Two types are comparable if:
            // - they are both integral or floating
            // - both classes or null, and assignment compatible
            // - both chandles or null
            // - both aggregates and equivalent
            if (bothNumeric) {
                good = true;

                // For equality and inequality, result is four state if either operand is four state.
                // For case equality and case inequality, result is never four state.
                // For wildcard equality / inequality, result is four state only if lhs is four state.
                if (syntax.kind == SyntaxKind::EqualityExpression ||
                    syntax.kind == SyntaxKind::InequalityExpression) {
                    result->type = singleBitType(compilation, lt, rt);
                }
                else if (syntax.kind == SyntaxKind::CaseEqualityExpression ||
                         syntax.kind == SyntaxKind::CaseInequalityExpression) {
                    result->type = &compilation.getBitType();
                }
                else {
                    result->type = lt->isFourState() ? &compilation.getLogicType() :
                                                       &compilation.getBitType();
                }

                // Result type is fixed but the two operands affect each other as they would in
                // other context-determined operators.
                auto nt = binaryOperatorType(compilation, lt, rt, false);
                contextDetermined(compilation, result->left_, *nt);
                contextDetermined(compilation, result->right_, *nt);
            }
            else if (lt->isAggregate() && lt->isEquivalent(*rt)) {
                // TODO: drill into the aggregate and figure out if it's all 2-state
                good = true;
                result->type = &compilation.getLogicType();
            }
            else if ((lt->isClass() && lt->isAssignmentCompatible(*rt)) ||
                     (rt->isClass() && rt->isAssignmentCompatible(*lt))) {
                good = true;
                result->type = &compilation.getBitType();
            }
            else if ((lt->isCHandle() || lt->isNull()) &&
                     (rt->isCHandle() || rt->isNull())) {
                good = true;
                result->type = &compilation.getBitType();
            }
            else {
                good = false;
            }
            break;
        case SyntaxKind::AssignmentExpression:
            // No particular restriction on types here. We'll handle
            // assignability below.
            good = true;
            break;
        default:
            THROW_UNREACHABLE;
    }

    auto location = syntax.operatorToken.location();
    if (!good) {
        auto& diag = compilation.addError(DiagCode::BadBinaryExpression, location);
        diag << *lt << *rt;
        diag << lhs.sourceRange;
        diag << rhs.sourceRange;
        return badExpr(compilation, result);
    }

    if (result->isAssignment()) {
        if (!checkLValue(compilation, lhs, location))
            return badExpr(compilation, result);

        // TODO: check for const assignment

        if (!lt->isAssignmentCompatible(*rt)) {
            DiagCode code = lt->isCastCompatible(*rt) ? DiagCode::NoImplicitConversion : DiagCode::BadAssignment;
            auto& diag = compilation.addError(code, location);
            diag << *rt << *lt;
            diag << lhs.sourceRange;
            diag << rhs.sourceRange;
            return badExpr(compilation, result);
        }

        // TODO: unify this with Compilation::bindAssignment
        if (lt->getBitWidth() > rt->getBitWidth()) {
            if (!lt->isFloating() && !rt->isFloating())
                rt = &compilation.getType(lt->getBitWidth(), rt->getIntegralFlags());
            else {
                if (lt->getBitWidth() > 32)
                    rt = &compilation.getRealType();
                else
                    rt = &compilation.getShortRealType();
            }
            // TODO: return value?
            Expression* r = &rhs;
            contextDetermined(compilation, r, *rt);
        }
        else {
            Expression* r = &rhs;
            selfDetermined(compilation, r);
        }
        result->type = lhs.type;
    }

    return *result;
}

Expression& ConditionalExpression::fromSyntax(Compilation& compilation, const ConditionalExpressionSyntax& syntax,
                                              const BindContext& context) {
    // TODO: handle the pattern matching conditional predicate case, rather than just assuming that it's a simple
    // expression
    ASSERT(syntax.predicate.conditions.count() == 1);
    Expression& pred = create(compilation, syntax.predicate.conditions[0]->expr, context);
    Expression& left = create(compilation, syntax.left, context);
    Expression& right = create(compilation, syntax.right, context);

    // TODO: handle non-integral and non-real types properly
    // force four-state return type for ambiguous condition case
    const Type* type = binaryOperatorType(compilation, left.type, right.type, true);
    return *compilation.emplace<ConditionalExpression>(*type, pred, left, right, syntax.sourceRange());
}

Expression& ElementSelectExpression::fromSyntax(Compilation& compilation, Expression& value,
                                                const ExpressionSyntax& syntax, SourceRange fullRange,
                                                const BindContext& context) {
    Expression& selector = create(compilation, syntax, context);
    auto result = compilation.emplace<ElementSelectExpression>(compilation.getErrorType(), value,
                                                               selector, fullRange);
    if (value.bad())
        return badExpr(compilation, result);

    const Type& valueType = value.type->getCanonicalType();
    if (!valueType.isIntegral()) {
        auto& diag = compilation.addError(DiagCode::BadIndexExpression, syntax.sourceRange());
        diag << value.sourceRange;
        diag << *value.type;
        return badExpr(compilation, result);
    }
    else if (valueType.isScalar()) {
        auto& diag = compilation.addError(DiagCode::CannotIndexScalar, syntax.sourceRange());
        diag << value.sourceRange;
        return badExpr(compilation, result);
    }
    else if (valueType.kind == SymbolKind::PackedArrayType) {
        result->type = &valueType.as<PackedArrayType>().elementType;
    }
    else {
        result->type = valueType.isFourState() ? &compilation.getLogicType() : &compilation.getBitType();
    }

    if (!selector.type->getCanonicalType().isIntegral()) {
        compilation.addError(DiagCode::IndexMustBeIntegral, selector.sourceRange);
        return badExpr(compilation, result);
    }

    return *result;
}

Expression& RangeSelectExpression::fromSyntax(Compilation& compilation, Expression& value,
                                              const RangeSelectSyntax& syntax, SourceRange fullRange,
                                              const BindContext& context) {
    Expression& left = create(compilation, syntax.left, context);
    Expression& right = create(compilation, syntax.right, context);

    RangeSelectionKind selectionKind;
    switch (syntax.kind) {
        case SyntaxKind::SimpleRangeSelect: selectionKind = RangeSelectionKind::Simple; break;
        case SyntaxKind::AscendingRangeSelect: selectionKind = RangeSelectionKind::IndexedUp; break;
        case SyntaxKind::DescendingRangeSelect: selectionKind = RangeSelectionKind::IndexedDown; break;
        default: THROW_UNREACHABLE;
    }

    auto result = compilation.emplace<RangeSelectExpression>(selectionKind, compilation.getErrorType(), value,
                                                             left, right, fullRange);
    if (value.bad())
        return badExpr(compilation, result);

    // TODO: clean this up
    bool down = value.type->as<IntegralType>().getBitVectorRange().isLittleEndian();
    int width;
    if (selectionKind == RangeSelectionKind::Simple)
        width = (down ? 1 : -1) * (int)(left.eval().integer().as<int64_t>().value() -
                                        right.eval().integer().as<int64_t>().value());
    else
        width = int(right.eval().integer().as<int64_t>().value());

    result->type = &compilation.getType((uint16_t)width, IntegralFlags::Unsigned);
    return *result;
}

Expression& ConcatenationExpression::fromSyntax(Compilation& compilation,
                                                const ConcatenationExpressionSyntax& syntax,
                                                const BindContext& context) {
    bool errored = false;
    bitmask<IntegralFlags> flags;
    bitwidth_t totalWidth = 0;
    SmallVectorSized<const Expression*, 8> buffer;

    for (auto argSyntax : syntax.expressions) {
        // Replications inside of concatenations have a special feature that allows them to have a width of zero.
        // Check now if we're going to be binding a replication and if so set an additional flag so that it knows
        // it's ok to have that zero count.
        Expression* arg;
        if (argSyntax->kind == SyntaxKind::MultipleConcatenationExpression)
            arg = &selfDetermined(compilation, *argSyntax, context.withFlags(BindFlags::InsideConcatenation));
        else
            arg = &selfDetermined(compilation, *argSyntax, context);
        buffer.append(arg);

        if (arg->bad()) {
            errored = true;
            break;
        }

        const Type& type = *arg->type;
        if (type.isVoid() && argSyntax->kind == SyntaxKind::MultipleConcatenationExpression)
            continue;

        if (!type.isIntegral()) {
            errored = true;
            compilation.addError(DiagCode::BadConcatExpression, arg->sourceRange);
            continue;
        }

        bitwidth_t newWidth = totalWidth + type.getBitWidth();
        if (newWidth < totalWidth) {
            errored = true;
            compilation.addError(DiagCode::ValueExceedsMaxBitWidth, syntax.sourceRange()) << (int)SVInt::MAX_BITS;
            break;
        }
        totalWidth = newWidth;

        if (type.isFourState())
            flags |= IntegralFlags::FourState;
    }

    if (errored) {
        return badExpr(compilation, compilation.emplace<ConcatenationExpression>(compilation.getErrorType(),
                                                                                 span<const Expression*>(),
                                                                                 syntax.sourceRange()));
    }

    return *compilation.emplace<ConcatenationExpression>(compilation.getType(totalWidth, flags),
                                                         buffer.copy(compilation), syntax.sourceRange());
}

Expression& ReplicationExpression::fromSyntax(Compilation& compilation,
                                              const MultipleConcatenationExpressionSyntax& syntax,
                                              const BindContext& context) {
    Expression& left = selfDetermined(compilation, syntax.expression,
                                      context.withFlags(BindFlags::IntegralConstant));
    Expression& right = selfDetermined(compilation, syntax.concatenation, context);

    auto result = compilation.emplace<ReplicationExpression>(compilation.getErrorType(), left,
                                                             right, syntax.sourceRange());

    // If left was not a constant we already issued an error, so just bail out.
    if (left.bad() || right.bad() || !left.constant || !left.constant->isInteger())
        return badExpr(compilation, result);

    const SVInt& value = left.constant->integer();
    if (!compilation.checkNoUnknowns(value, left.sourceRange) ||
        !compilation.checkPositive(value, left.sourceRange))
        return badExpr(compilation, result);

    if (value == 0) {
        if ((context.flags & BindFlags::InsideConcatenation) == 0) {
            compilation.addError(DiagCode::ReplicationZeroOutsideConcat, left.sourceRange);
            return badExpr(compilation, result);
        }

        // Use a placeholder type here to indicate to the parent concatenation that this had a zero width.
        result->type = &compilation.getVoidType();
        return *result;
    }

    auto width = compilation.checkValidBitWidth(value * right.type->getBitWidth(), syntax.sourceRange());
    if (!width)
        return badExpr(compilation, result);

    result->type = &compilation.getType(*width, right.type->isFourState() ? IntegralFlags::FourState : IntegralFlags::TwoState);
    return *result;
}

Expression& CallExpression::fromSyntax(Compilation& compilation, const InvocationExpressionSyntax& syntax,
                                       const BindContext& context) {
    // TODO: check for something other than a simple name on the LHS
    auto name = syntax.left.getFirstToken();

    // TODO: name syntax on the LHS in parser?
    LookupResult result;
    context.scope.lookupName(syntax.left.as<NameSyntax>(), context.lookupLocation, LookupNameKind::Callable, result);

    const Symbol* symbol = result.found;
    ASSERT(symbol && symbol->kind == SymbolKind::Subroutine);

    auto actualArgs = syntax.arguments->parameters;
    const SubroutineSymbol& subroutine = symbol->as<SubroutineSymbol>();

    // TODO: handle too few args as well, which requires looking at default values
    auto formalArgs = subroutine.arguments;
    if (formalArgs.size() < actualArgs.count()) {
        auto& diag = compilation.addError(DiagCode::TooManyArguments, name.location());
        diag << syntax.left.sourceRange();
        diag << formalArgs.size();
        diag << actualArgs.count();
        return badExpr(compilation, nullptr);
    }

    // TODO: handle named arguments in addition to ordered
    SmallVectorSized<const Expression*, 8> buffer;
    for (uint32_t i = 0; i < actualArgs.count(); i++) {
        const auto& arg = actualArgs[i]->as<OrderedArgumentSyntax>();
        buffer.append(&Expression::bind(compilation, *formalArgs[i]->type, arg.expr,
                                        arg.getFirstToken().location(), context));
    }

    return *compilation.emplace<CallExpression>(subroutine, buffer.copy(compilation), syntax.sourceRange());
}

bool BinaryExpression::isAssignment() const {
    switch (op) {
        case BinaryOperator::Assignment:
        case BinaryOperator::AddAssignment:
        case BinaryOperator::SubtractAssignment:
        case BinaryOperator::MultiplyAssignment:
        case BinaryOperator::DivideAssignment:
        case BinaryOperator::ModAssignment:
        case BinaryOperator::AndAssignment:
        case BinaryOperator::OrAssignment:
        case BinaryOperator::XorAssignment:
        case BinaryOperator::LogicalLeftShiftAssignment:
        case BinaryOperator::LogicalRightShiftAssignment:
        case BinaryOperator::ArithmeticLeftShiftAssignment:
        case BinaryOperator::ArithmeticRightShiftAssignment:
            return true;
        default:
            return false;
    }
}

UnaryOperator getUnaryOperator(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::UnaryPlusExpression: return UnaryOperator::Plus;
        case SyntaxKind::UnaryMinusExpression: return UnaryOperator::Minus;
        case SyntaxKind::UnaryBitwiseNotExpression: return UnaryOperator::BitwiseNot;
        case SyntaxKind::UnaryBitwiseAndExpression: return UnaryOperator::BitwiseAnd;
        case SyntaxKind::UnaryBitwiseOrExpression: return UnaryOperator::BitwiseOr;
        case SyntaxKind::UnaryBitwiseXorExpression: return UnaryOperator::BitwiseXor;
        case SyntaxKind::UnaryBitwiseNandExpression: return UnaryOperator::BitwiseNand;
        case SyntaxKind::UnaryBitwiseNorExpression: return UnaryOperator::BitwiseNor;
        case SyntaxKind::UnaryBitwiseXnorExpression: return UnaryOperator::BitwiseXnor;
        case SyntaxKind::UnaryLogicalNotExpression: return UnaryOperator::LogicalNot;
        case SyntaxKind::UnaryPreincrementExpression: return UnaryOperator::Preincrement;
        case SyntaxKind::UnaryPredecrementExpression: return UnaryOperator::Predecrement;
        case SyntaxKind::PostincrementExpression: return UnaryOperator::Postincrement;
        case SyntaxKind::PostdecrementExpression: return UnaryOperator::Postdecrement;
        default: THROW_UNREACHABLE;
    }
}

BinaryOperator getBinaryOperator(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::AddExpression: return BinaryOperator::Add;
        case SyntaxKind::SubtractExpression: return BinaryOperator::Subtract;
        case SyntaxKind::MultiplyExpression: return BinaryOperator::Multiply;
        case SyntaxKind::DivideExpression: return BinaryOperator::Divide;
        case SyntaxKind::ModExpression: return BinaryOperator::Mod;
        case SyntaxKind::BinaryAndExpression: return BinaryOperator::BinaryAnd;
        case SyntaxKind::BinaryOrExpression: return BinaryOperator::BinaryOr;
        case SyntaxKind::BinaryXorExpression: return BinaryOperator::BinaryXor;
        case SyntaxKind::BinaryXnorExpression: return BinaryOperator::BinaryXnor;
        case SyntaxKind::EqualityExpression: return BinaryOperator::Equality;
        case SyntaxKind::InequalityExpression: return BinaryOperator::Inequality;
        case SyntaxKind::CaseEqualityExpression: return BinaryOperator::CaseEquality;
        case SyntaxKind::CaseInequalityExpression: return BinaryOperator::CaseInequality;
        case SyntaxKind::GreaterThanEqualExpression: return BinaryOperator::GreaterThanEqual;
        case SyntaxKind::GreaterThanExpression: return BinaryOperator::GreaterThan;
        case SyntaxKind::LessThanEqualExpression: return BinaryOperator::LessThanEqual;
        case SyntaxKind::LessThanExpression: return BinaryOperator::LessThan;
        case SyntaxKind::WildcardEqualityExpression: return BinaryOperator::WildcardEquality;
        case SyntaxKind::WildcardInequalityExpression: return BinaryOperator::WildcardInequality;
        case SyntaxKind::LogicalAndExpression: return BinaryOperator::LogicalAnd;
        case SyntaxKind::LogicalOrExpression: return BinaryOperator::LogicalOr;
        case SyntaxKind::LogicalImplicationExpression: return BinaryOperator::LogicalImplication;
        case SyntaxKind::LogicalEquivalenceExpression: return BinaryOperator::LogicalEquivalence;
        case SyntaxKind::LogicalShiftLeftExpression: return BinaryOperator::LogicalShiftLeft;
        case SyntaxKind::LogicalShiftRightExpression: return BinaryOperator::LogicalShiftRight;
        case SyntaxKind::ArithmeticShiftLeftExpression: return BinaryOperator::ArithmeticShiftLeft;
        case SyntaxKind::ArithmeticShiftRightExpression: return BinaryOperator::ArithmeticShiftRight;
        case SyntaxKind::PowerExpression: return BinaryOperator::Power;
        case SyntaxKind::AssignmentExpression: return BinaryOperator::Assignment;
        case SyntaxKind::AddAssignmentExpression: return BinaryOperator::AddAssignment;
        case SyntaxKind::SubtractAssignmentExpression: return BinaryOperator::SubtractAssignment;
        case SyntaxKind::MultiplyAssignmentExpression: return BinaryOperator::MultiplyAssignment;
        case SyntaxKind::DivideAssignmentExpression: return BinaryOperator::DivideAssignment;
        case SyntaxKind::ModAssignmentExpression: return BinaryOperator::ModAssignment;
        case SyntaxKind::AndAssignmentExpression: return BinaryOperator::AndAssignment;
        case SyntaxKind::OrAssignmentExpression: return BinaryOperator::OrAssignment;
        case SyntaxKind::XorAssignmentExpression: return BinaryOperator::XorAssignment;
        case SyntaxKind::LogicalLeftShiftAssignmentExpression: return BinaryOperator::LogicalLeftShiftAssignment;
        case SyntaxKind::LogicalRightShiftAssignmentExpression: return BinaryOperator::LogicalRightShiftAssignment;
        case SyntaxKind::ArithmeticLeftShiftAssignmentExpression: return BinaryOperator::ArithmeticLeftShiftAssignment;
        case SyntaxKind::ArithmeticRightShiftAssignmentExpression: return BinaryOperator::ArithmeticRightShiftAssignment;
        default: THROW_UNREACHABLE;
    }
}

}
