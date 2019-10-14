//------------------------------------------------------------------------------
// Expressions.cpp
// Expression creation and analysis.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/Expressions.h"

#include <nlohmann/json.hpp>

#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/symbols/TypeSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/util/StackContainer.h"

namespace {

using namespace slang;

const Type* binaryOperatorType(Compilation& compilation, const Type* lt, const Type* rt,
                               bool forceFourState) {
    if (!lt->isNumeric() || !rt->isNumeric())
        return &compilation.getErrorType();

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
    else if (lt->isEnum() && rt->isEnum() && lt->isMatching(*rt)) {
        // If both sides are the same enum type, preserve that in the output type.
        // NOTE: This specifically ignores the forceFourState option.
        return lt;
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

const Type& getIndexedType(Compilation& compilation, const BindContext& context,
                           const Type& valueType, SourceRange exprRange, SourceRange valueRange,
                           bool isRangeSelect) {
    const Type& ct = valueType.getCanonicalType();
    if (ct.kind == SymbolKind::UnpackedArrayType) {
        return ct.as<UnpackedArrayType>().elementType;
    }
    else if (ct.kind == SymbolKind::PackedArrayType) {
        return ct.as<PackedArrayType>().elementType;
    }
    else if (ct.kind == SymbolKind::StringType && !isRangeSelect) {
        return compilation.getByteType();
    }
    else if (!ct.isIntegral()) {
        auto& diag = context.addDiag(diag::BadIndexExpression, exprRange);
        diag << valueRange;
        diag << valueType;
        return compilation.getErrorType();
    }
    else if (ct.isScalar()) {
        auto& diag = context.addDiag(diag::CannotIndexScalar, exprRange);
        diag << valueRange;
        return compilation.getErrorType();
    }
    else if (ct.isFourState()) {
        return compilation.getLogicType();
    }
    else {
        return compilation.getBitType();
    }
}

struct ToJsonVisitor {
    template<typename T>
    void visit(const T& expr, json& j) {
        j["kind"] = toString(expr.kind);
        j["type"] = *expr.type;

        if (expr.constant)
            j["constant"] = *expr.constant;

        if constexpr (!std::is_same_v<Expression, T>) {
            expr.toJson(j);
        }
    }

    void visitInvalid(const Expression& expr, json& j) { visit(expr.as<InvalidExpression>(), j); }
};

void checkBindFlags(const Expression& expr, const BindContext& context) {
    if ((context.flags & BindFlags::Constant) == 0)
        return;

    EvalContext verifyContext(context.scope, EvalFlags::IsVerifying);
    bool canBeConst = expr.verifyConstant(verifyContext);
    verifyContext.reportDiags(context, expr.sourceRange);
    if (!canBeConst)
        return;

    EvalContext evalContext(context.scope);
    expr.eval(evalContext);
    evalContext.reportDiags(context, expr.sourceRange);
}

bool recurseCheckEnum(const Expression& expr) {
    switch (expr.kind) {
        case ExpressionKind::UnbasedUnsizedIntegerLiteral:
        case ExpressionKind::NamedValue:
        case ExpressionKind::MemberAccess:
            return true;
        case ExpressionKind::IntegerLiteral:
            return expr.as<IntegerLiteral>().isDeclaredUnsized;
        case ExpressionKind::UnaryOp:
            return recurseCheckEnum(expr.as<UnaryExpression>().operand());
        case ExpressionKind::BinaryOp: {
            auto& bin = expr.as<BinaryExpression>();
            return recurseCheckEnum(bin.left()) && recurseCheckEnum(bin.right());
        }
        case ExpressionKind::ConditionalOp: {
            auto& cond = expr.as<ConditionalExpression>();
            return recurseCheckEnum(cond.left()) && recurseCheckEnum(cond.right());
        }
        case ExpressionKind::Conversion: {
            auto& conv = expr.as<ConversionExpression>();
            return conv.isImplicit && recurseCheckEnum(conv.operand());
        }
        default:
            return false;
    }
}

bool checkEnumInitializer(const BindContext& context, const Type& lt, const Expression& rhs) {
    // [6.19] says that the initializer for an enum value must be an integer expression that
    // does not truncate any bits. Furthermore, if a sized literal constant is used, it must
    // be sized exactly to the size of the enum base type. It's not well defined what happens
    // if the sized constant is used further down in some sub-expression, so what we check here
    // is cases where it seems ok to suppress the error:
    // - Unsized literals, variable references
    // - Unary, binary, conditional expressions of the above

    const Type& rt = *rhs.type;
    if (!rt.isIntegral()) {
        context.addDiag(diag::ValueMustBeIntegral, rhs.sourceRange);
        return false;
    }

    if (lt.getBitWidth() == rt.getBitWidth())
        return true;

    if (!recurseCheckEnum(rhs)) {
        auto& diag = context.addDiag(diag::EnumValueSizeMismatch, rhs.sourceRange);
        diag << rt.getBitWidth() << lt.getBitWidth();
        return false;
    }

    return true;
}

// This function exists to handle a case like:
//      integer i;
//      enum { A, B } foo;
//      initial foo = i ? A : B;
// This would otherwise be disallowed because using a 4-state predicate
// means the result of the conditional operator would be 4-state, and
// the enum base type is not 4-state.
bool isSameEnum(const Expression& expr, const Type& enumType) {
    if (expr.kind == ExpressionKind::ConditionalOp) {
        auto& cond = expr.as<ConditionalExpression>();
        return isSameEnum(cond.left(), enumType) && isSameEnum(cond.right(), enumType);
    }
    return expr.type->isMatching(enumType);
}

} // namespace

namespace slang {

// This visitor handles inserting implicit conversions into an expression tree where necessary.
// SystemVerilog has an additional weird feature where the type of one branch of an expression
// tree can bubble up and then propagate back down a different branch, which is also implemented
// here.
struct Expression::PropagationVisitor {
    HAS_METHOD_TRAIT(propagateType);

    const BindContext& context;
    const Type& newType;

    PropagationVisitor(const BindContext& context, const Type& newType) :
        context(context), newType(newType) {}

    template<typename T>
    Expression& visit(T& expr) {
        if (expr.bad())
            return expr;

        if (newType.isError()) {
            expr.type = &newType;
            return expr;
        }

        // If the new type is equivalent to the old type, there's no need for a
        // conversion. Otherwise if both types are integral or both are real, we have to
        // check if the conversion should be pushed further down the tree. Otherwise we
        // should insert the implicit conversion here.
        bool needConversion = !newType.isEquivalent(*expr.type);
        if constexpr (has_propagateType_v<T, bool, const BindContext&, const Type&>) {
            if ((newType.isFloating() && expr.type->isFloating()) ||
                (newType.isIntegral() && expr.type->isIntegral()) || newType.isString()) {

                if (expr.propagateType(context, newType))
                    needConversion = false;
            }
        }

        Expression* result = &expr;
        if (needConversion)
            result = &Expression::implicitConversion(context, newType, expr);

        // Try to fold any constant values. If this results in diagnostics we
        // don't save the value here to force re-evaluation later on.
        ASSERT(!result->constant);
        EvalContext evalContext(context.scope);
        ConstantValue value = result->eval(evalContext);
        if (value && evalContext.getDiagnostics().empty())
            result->constant = context.scope.getCompilation().allocConstant(std::move(value));
        return *result;
    }

    Expression& visitInvalid(Expression& expr) { return expr; }
};

const InvalidExpression InvalidExpression::Instance(nullptr, ErrorType::Instance);

const Expression& Expression::bind(const ExpressionSyntax& syntax, const BindContext& context,
                                   bitmask<BindFlags> extraFlags) {
    const Expression& result =
        selfDetermined(context.scope.getCompilation(), syntax, context, extraFlags);
    checkBindFlags(result, context.resetFlags(extraFlags));
    return result;
}

const Expression& Expression::bind(const Type& lhs, const ExpressionSyntax& rhs,
                                   SourceLocation location, const BindContext& context) {
    Compilation& comp = context.scope.getCompilation();
    Expression& expr = create(comp, rhs, context, BindFlags::None, &lhs);

    const Expression& result = convertAssignment(context, lhs, expr, location);
    checkBindFlags(result, context);
    return result;
}

bool Expression::bindCaseExpressions(const BindContext& context, TokenKind caseKind,
                                     const ExpressionSyntax& valueExpr,
                                     span<const ExpressionSyntax* const> expressions,
                                     SmallVector<const Expression*>& results) {

    Compilation& comp = context.scope.getCompilation();
    Expression& valueRes = create(comp, valueExpr, context);
    results.append(&valueRes);

    const Type* type = valueRes.type;
    bool bad = valueRes.bad();
    bool wildcard = caseKind != TokenKind::CaseKeyword;
    bool canBeStrings = valueRes.isImplicitString();

    if ((!wildcard && type->isAggregate()) || (wildcard && !type->isIntegral())) {
        if (!bad) {
            context.addDiag(diag::InvalidCaseStmtType, valueRes.sourceRange)
                << *type << getTokenKindText(caseKind);
            bad = true;
        }
    }

    // We need to find a common type across all expressions. If this is for a wildcard
    // case statement, the types can only be integral. Otherwise all singular types are allowed.
    for (auto expr : expressions) {
        Expression* bound = &create(comp, *expr, context);
        results.append(bound);
        bad |= bound->bad();
        if (bad)
            continue;

        const Type& bt = *bound->type;
        if (wildcard) {
            if (!bt.isIntegral()) {
                context.addDiag(diag::InvalidCaseStmtType, bound->sourceRange)
                    << bt << getTokenKindText(caseKind);
                bad = true;
            }
            else {
                type = binaryOperatorType(comp, type, &bt, false);
            }
        }
        else {
            if (canBeStrings && !bound->isImplicitString())
                canBeStrings = false;

            if (bt.isNumeric() && type->isNumeric()) {
                type = binaryOperatorType(comp, type, &bt, false);
            }
            else if ((bt.isClass() && bt.isAssignmentCompatible(*type)) ||
                     (type->isClass() && type->isAssignmentCompatible(bt))) {
                // ok
            }
            else if ((bt.isCHandle() || bt.isNull()) && (type->isCHandle() || type->isNull())) {
                // ok
            }
            else if (canBeStrings) {
                // If canBeStrings is still true, it means either this specific type or
                // the common type (or both) are of type string. This is ok, but force
                // all further expressions to also be strings (or implicitly
                // convertible to them).
                type = &comp.getStringType();
            }
            else if (bt.isAggregate()) {
                // Aggregates are just never allowed in case expressions.
                context.addDiag(diag::InvalidCaseStmtType, bound->sourceRange)
                    << bt << getTokenKindText(caseKind);
                bad = true;
            }
            else {
                // Couldn't find a common type.
                context.addDiag(diag::NoCommonCaseStmtType, bound->sourceRange) << bt << *type;
                bad = true;
            }
        }
    }

    if (bad)
        return false;

    size_t index = 0;
    for (auto result : results) {
        // const_casts here are because we want the result array to be constant and
        // don't want to waste time / space allocating another array here locally just
        // to immediately copy it to the output.
        Expression* expr = const_cast<Expression*>(result);

        if (type->isNumeric() || type->isString())
            contextDetermined(context, expr, *type);
        else
            selfDetermined(context, expr);

        checkBindFlags(*expr, context);
        results[index++] = expr;
    }

    return true;
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
        case ExpressionKind::Concatenation: {
            auto& concat = as<ConcatenationExpression>();
            for (auto op : concat.operands()) {
                if (!op->isLValue())
                    return false;
            }
            return true;
        }
        default:
            return false;
    }
}

bool Expression::isImplicitString() const {
    if (type->isString())
        return true;

    switch (kind) {
        case ExpressionKind::StringLiteral:
            return true;
        case ExpressionKind::UnaryOp:
            return as<UnaryExpression>().operand().isImplicitString();
        case ExpressionKind::BinaryOp: {
            auto& op = as<BinaryExpression>();
            return op.left().isImplicitString() || op.right().isImplicitString();
        }
        case ExpressionKind::ConditionalOp: {
            auto& op = as<ConditionalExpression>();
            return op.left().isImplicitString() || op.right().isImplicitString();
        }
        case ExpressionKind::Concatenation: {
            auto& concat = as<ConcatenationExpression>();
            for (auto op : concat.operands()) {
                if (op->isImplicitString())
                    return true;
            }
            return false;
        }
        case ExpressionKind::Replication: {
            auto& repl = as<ReplicationExpression>();
            return repl.concat().isImplicitString();
        }
        default:
            return false;
    }
}

void to_json(json& j, const Expression& expr) {
    ToJsonVisitor visitor;
    expr.visit(visitor, j);
}

Expression& Expression::create(Compilation& compilation, const ExpressionSyntax& syntax,
                               const BindContext& ctx, bitmask<BindFlags> extraFlags,
                               const Type* assignmentTarget) {
    BindContext context = ctx.resetFlags(extraFlags);
    Expression* result;
    switch (syntax.kind) {
        case SyntaxKind::BadExpression:
            result = &badExpr(compilation, nullptr);
            break;
        case SyntaxKind::NullLiteralExpression:
            result = &NullLiteral::fromSyntax(compilation, syntax.as<LiteralExpressionSyntax>());
            break;
        case SyntaxKind::StringLiteralExpression:
            result = &StringLiteral::fromSyntax(compilation, syntax.as<LiteralExpressionSyntax>());
            break;
        case SyntaxKind::RealLiteralExpression:
            result = &RealLiteral::fromSyntax(compilation, syntax.as<LiteralExpressionSyntax>());
            break;
        case SyntaxKind::IntegerLiteralExpression:
            result = &IntegerLiteral::fromSyntax(compilation, syntax.as<LiteralExpressionSyntax>());
            break;
        case SyntaxKind::UnbasedUnsizedLiteralExpression:
            result = &UnbasedUnsizedIntegerLiteral::fromSyntax(
                compilation, syntax.as<LiteralExpressionSyntax>());
            break;
        case SyntaxKind::IntegerVectorExpression:
            result = &IntegerLiteral::fromSyntax(compilation,
                                                 syntax.as<IntegerVectorExpressionSyntax>());
            break;
        case SyntaxKind::ParenthesizedExpression:
            result = &create(compilation, *syntax.as<ParenthesizedExpressionSyntax>().expression,
                             context, extraFlags, assignmentTarget);
            break;
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
            result = &UnaryExpression::fromSyntax(
                compilation, syntax.as<PrefixUnaryExpressionSyntax>(), context);
            break;
        case SyntaxKind::PostincrementExpression:
        case SyntaxKind::PostdecrementExpression:
            result = &UnaryExpression::fromSyntax(
                compilation, syntax.as<PostfixUnaryExpressionSyntax>(), context);
            break;
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
            result = &BinaryExpression::fromSyntax(compilation, syntax.as<BinaryExpressionSyntax>(),
                                                   context);
            break;
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
            result = &AssignmentExpression::fromSyntax(
                compilation, syntax.as<BinaryExpressionSyntax>(), context);
            break;
        case SyntaxKind::InvocationExpression:
            result = &CallExpression::fromSyntax(compilation,
                                                 syntax.as<InvocationExpressionSyntax>(), context);
            break;
        case SyntaxKind::ConditionalExpression:
            result = &ConditionalExpression::fromSyntax(
                compilation, syntax.as<ConditionalExpressionSyntax>(), context, assignmentTarget);
            break;
        case SyntaxKind::MemberAccessExpression:
            result = &MemberAccessExpression::fromSyntax(
                compilation, syntax.as<MemberAccessExpressionSyntax>(), nullptr, context);
            break;
        case SyntaxKind::ConcatenationExpression:
            result = &ConcatenationExpression::fromSyntax(
                compilation, syntax.as<ConcatenationExpressionSyntax>(), context);
            break;
        case SyntaxKind::MultipleConcatenationExpression:
            result = &ReplicationExpression::fromSyntax(
                compilation, syntax.as<MultipleConcatenationExpressionSyntax>(), context);
            break;
        case SyntaxKind::ElementSelectExpression:
            result = &bindSelectExpression(compilation, syntax.as<ElementSelectExpressionSyntax>(),
                                           context);
            break;
        case SyntaxKind::CastExpression:
            result = &ConversionExpression::fromSyntax(compilation,
                                                       syntax.as<CastExpressionSyntax>(), context);
            break;
        case SyntaxKind::SignedCastExpression:
            result = &ConversionExpression::fromSyntax(
                compilation, syntax.as<SignedCastExpressionSyntax>(), context);
            break;
        case SyntaxKind::AssignmentPatternExpression:
            result =
                &bindAssignmentPattern(compilation, syntax.as<AssignmentPatternExpressionSyntax>(),
                                       context, assignmentTarget);
            break;
        case SyntaxKind::AcceptOnPropertyExpression:
        case SyntaxKind::AlwaysPropertyExpression:
        case SyntaxKind::AndSequenceExpression:
        case SyntaxKind::ArrayOrRandomizeMethodExpression:
        case SyntaxKind::BinarySequenceDelayExpression:
        case SyntaxKind::DefaultPatternKeyExpression:
        case SyntaxKind::ElementSelect:
        case SyntaxKind::EmptyQueueExpression:
        case SyntaxKind::EventuallyPropertyExpression:
        case SyntaxKind::ExpressionOrDist:
        case SyntaxKind::IffPropertyExpression:
        case SyntaxKind::ImpliesPropertyExpression:
        case SyntaxKind::InsideExpression:
        case SyntaxKind::IntersectSequenceExpression:
        case SyntaxKind::MinTypMaxExpression:
        case SyntaxKind::NewArrayExpression:
        case SyntaxKind::NewClassExpression:
        case SyntaxKind::NewExpression:
        case SyntaxKind::NextTimePropertyExpression:
        case SyntaxKind::NonOverlappedFollowedByPropertyExpression:
        case SyntaxKind::NonOverlappedImplicationPropertyExpression:
        case SyntaxKind::NonblockingAssignmentExpression:
        case SyntaxKind::OneStepLiteralExpression:
        case SyntaxKind::OrSequenceExpression:
        case SyntaxKind::OverlappedFollowedByPropertyExpression:
        case SyntaxKind::OverlappedImplicationPropertyExpression:
        case SyntaxKind::RejectOnPropertyExpression:
        case SyntaxKind::SAlwaysPropertyExpression:
        case SyntaxKind::SEventuallyPropertyExpression:
        case SyntaxKind::SNextTimePropertyExpression:
        case SyntaxKind::SUntilPropertyExpression:
        case SyntaxKind::SUntilWithPropertyExpression:
        case SyntaxKind::StreamingConcatenationExpression:
        case SyntaxKind::SyncAcceptOnPropertyExpression:
        case SyntaxKind::SyncRejectOnPropertyExpression:
        case SyntaxKind::TaggedUnionExpression:
        case SyntaxKind::ThroughoutSequenceExpression:
        case SyntaxKind::TimeLiteralExpression:
        case SyntaxKind::TimingControlExpression:
        case SyntaxKind::TimingControlExpressionConcatenation:
        case SyntaxKind::UnaryNotPropertyExpression:
        case SyntaxKind::UnarySequenceDelayExpression:
        case SyntaxKind::UnarySequenceEventExpression:
        case SyntaxKind::UntilPropertyExpression:
        case SyntaxKind::UntilWithPropertyExpression:
        case SyntaxKind::WildcardLiteralExpression:
        case SyntaxKind::WithClause:
        case SyntaxKind::WithinSequenceExpression:
            context.addDiag(diag::NotYetSupported, syntax.sourceRange());
            result = &badExpr(compilation, nullptr);
            break;
        default:
            if (NameSyntax::isKind(syntax.kind)) {
                result = &bindName(compilation, syntax.as<NameSyntax>(), nullptr, context);
                break;
            }
            else if (DataTypeSyntax::isKind(syntax.kind)) {
                result = &DataTypeExpression::fromSyntax(compilation, syntax.as<DataTypeSyntax>(),
                                                         context);
                break;
            }
            THROW_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

Expression& Expression::bindName(Compilation& compilation, const NameSyntax& syntax,
                                 const InvocationExpressionSyntax* invocation,
                                 const BindContext& context) {
    bitmask<LookupFlags> flags = LookupFlags::None;
    if (invocation && invocation->arguments)
        flags |= LookupFlags::AllowDeclaredAfter;
    if ((context.flags & BindFlags::Constant) || (context.flags & BindFlags::NoHierarchicalNames))
        flags |= LookupFlags::Constant;

    LookupResult result;
    context.scope.lookupName(syntax, context.lookupLocation, flags, result);

    if (result.hasError()) {
        // If we failed to find the symbol because of restrictions on hierarchical names
        // inside constant expressions (which we know if evalContext is set) then issue
        // a backtrace to give the user a bit more context.
        if (!result.found && result.isHierarchical && context.evalContext) {
            Diagnostics stack;
            context.evalContext->reportStack(stack);

            Diagnostics diagnostics;
            diagnostics.appendRange(result.getDiagnostics());

            Diagnostic& first = diagnostics.front();
            for (auto& diag : stack)
                first.addNote(diag);

            compilation.addDiagnostics(diagnostics);
        }
        else {
            compilation.addDiagnostics(result.getDiagnostics());
        }
    }

    SourceRange callRange = invocation ? invocation->sourceRange() : syntax.sourceRange();
    if (result.systemSubroutine) {
        // There won't be any selectors here; this gets checked in the lookup call.
        ASSERT(result.selectors.empty());
        return CallExpression::fromLookup(compilation, result.systemSubroutine, invocation,
                                          callRange, context);
    }

    const Symbol* symbol = result.found;
    if (!symbol)
        return badExpr(compilation, nullptr);

    if (symbol->isType() && (context.flags & BindFlags::AllowDataType) != 0) {
        // We looked up a named data type and we were allowed to do so, so return it.
        ASSERT(!invocation);
        const Type& resultType = Type::fromLookupResult(compilation, result, syntax,
                                                        context.lookupLocation, context.scope);
        return *compilation.emplace<DataTypeExpression>(resultType, syntax.sourceRange());
    }

    Expression* expr;
    if (symbol->kind == SymbolKind::Subroutine) {
        expr = &CallExpression::fromLookup(compilation, &symbol->as<SubroutineSymbol>(), invocation,
                                           callRange, context);
        invocation = nullptr;
    }
    else {
        expr = &NamedValueExpression::fromSymbol(context.scope, *symbol, result.isHierarchical,
                                                 syntax.sourceRange());
    }

    // Drill down into member accesses.
    for (const auto& selector : result.selectors) {
        if (expr->bad())
            return *expr;

        auto memberSelect = std::get_if<LookupResult::MemberSelector>(&selector);
        if (memberSelect) {
            expr = &MemberAccessExpression::fromSelector(compilation, *expr, *memberSelect,
                                                         invocation, context);
            if (expr->kind == ExpressionKind::Call)
                invocation = nullptr;
        }
        else {
            // Element / range selectors.
            const ElementSelectSyntax* selectSyntax =
                std::get<const ElementSelectSyntax*>(selector);
            expr = &bindSelector(compilation, *expr, *selectSyntax, context);
        }
    }

    // If we require a subroutine, enforce that now. The invocation syntax will have been
    // nulled out if we used it above.
    if (invocation && !expr->bad()) {
        SourceLocation loc = invocation->arguments ? invocation->arguments->openParen.location()
                                                   : syntax.getFirstToken().location();
        auto& diag = context.addDiag(diag::ExpressionNotCallable, loc);
        diag << syntax.sourceRange();
        return badExpr(compilation, nullptr);
    }

    return *expr;
}

Expression& Expression::bindSelectExpression(Compilation& compilation,
                                             const ElementSelectExpressionSyntax& syntax,
                                             const BindContext& context) {
    Expression& value = create(compilation, *syntax.left, context);
    return bindSelector(compilation, value, *syntax.select, context);
}

Expression& Expression::bindSelector(Compilation& compilation, Expression& value,
                                     const ElementSelectSyntax& syntax,
                                     const BindContext& context) {
    const SelectorSyntax* selector = syntax.selector;
    if (!selector) {
        context.addDiag(diag::ExpectedExpression, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    // The full source range of the expression includes the value and the selector syntax.
    SourceRange fullRange = { value.sourceRange.start(), syntax.sourceRange().end() };

    switch (selector->kind) {
        case SyntaxKind::BitSelect:
            return ElementSelectExpression::fromSyntax(
                compilation, value, *selector->as<BitSelectSyntax>().expr, fullRange, context);
        case SyntaxKind::SimpleRangeSelect:
        case SyntaxKind::AscendingRangeSelect:
        case SyntaxKind::DescendingRangeSelect:
            return RangeSelectExpression::fromSyntax(
                compilation, value, selector->as<RangeSelectSyntax>(), fullRange, context);
        default:
            THROW_UNREACHABLE;
    }
}

Expression& Expression::bindAssignmentPattern(Compilation& comp,
                                              const AssignmentPatternExpressionSyntax& syntax,
                                              const BindContext& context,
                                              const Type* assignmentTarget) {
    if (syntax.type)
        assignmentTarget = &comp.getType(*syntax.type, context.lookupLocation, context.scope);

    if (!assignmentTarget || assignmentTarget->isError()) {
        if (!assignmentTarget)
            context.addDiag(diag::AssignmentPatternNoContext, syntax.sourceRange());
        return badExpr(comp, nullptr);
    }

    SourceRange range = syntax.sourceRange();
    const Type& type = *assignmentTarget;
    const Scope* structScope = nullptr;
    const Type* elementType = nullptr;
    bitwidth_t numElements = 0;

    auto& ct = type.getCanonicalType();
    if (ct.kind == SymbolKind::PackedStructType)
        structScope = &ct.as<PackedStructType>();
    else if (ct.kind == SymbolKind::UnpackedStructType)
        structScope = &ct.as<UnpackedStructType>();
    else if (ct.kind == SymbolKind::UnpackedArrayType) {
        auto& ua = ct.as<UnpackedArrayType>();
        elementType = &ua.elementType;
        numElements = ua.range.width();
    }
    else if (ct.isIntegral() && ct.kind != SymbolKind::ScalarType) {
        elementType = ct.isFourState() ? &comp.getLogicType() : &comp.getBitType();
        numElements = ct.getBitWidth();
    }
    else {
        context.addDiag(diag::BadAssignmentPatternType, range) << type;
        return badExpr(comp, nullptr);
    }

    AssignmentPatternSyntax& p = *syntax.pattern;
    if (structScope) {
        switch (p.kind) {
            case SyntaxKind::SimpleAssignmentPattern:
                return SimpleAssignmentPatternExpression::forStruct(
                    comp, p.as<SimpleAssignmentPatternSyntax>(), context, type, *structScope,
                    range);
            case SyntaxKind::StructuredAssignmentPattern:
                return StructuredAssignmentPatternExpression::forStruct(
                    comp, p.as<StructuredAssignmentPatternSyntax>(), context, type, *structScope,
                    range);
            case SyntaxKind::ReplicatedAssignmentPattern:
                return ReplicatedAssignmentPatternExpression::forStruct(
                    comp, p.as<ReplicatedAssignmentPatternSyntax>(), context, type, *structScope,
                    range);
            default:
                THROW_UNREACHABLE;
        }
    }
    else {
        switch (p.kind) {
            case SyntaxKind::SimpleAssignmentPattern:
                return SimpleAssignmentPatternExpression::forArray(
                    comp, p.as<SimpleAssignmentPatternSyntax>(), context, type, *elementType,
                    numElements, range);
            case SyntaxKind::StructuredAssignmentPattern:
                return StructuredAssignmentPatternExpression::forArray(
                    comp, p.as<StructuredAssignmentPatternSyntax>(), context, type, *elementType,
                    range);
            case SyntaxKind::ReplicatedAssignmentPattern:
                return ReplicatedAssignmentPatternExpression::forArray(
                    comp, p.as<ReplicatedAssignmentPatternSyntax>(), context, type, *elementType,
                    numElements, range);
            default:
                THROW_UNREACHABLE;
        }
    }
}

void Expression::contextDetermined(const BindContext& context, Expression*& expr,
                                   const Type& newType) {
    PropagationVisitor visitor(context, newType);
    expr = &expr->visit(visitor);
}

void Expression::selfDetermined(const BindContext& context, Expression*& expr) {
    ASSERT(expr->type);
    PropagationVisitor visitor(context, *expr->type);
    expr = &expr->visit(visitor);
}

Expression& Expression::selfDetermined(Compilation& compilation, const ExpressionSyntax& syntax,
                                       const BindContext& context, bitmask<BindFlags> extraFlags) {
    Expression* expr = &create(compilation, syntax, context, extraFlags);
    selfDetermined(context, expr);
    return *expr;
}

Expression& Expression::implicitConversion(const BindContext& context, const Type& targetType,
                                           Expression& expr) {
    ASSERT(targetType.isAssignmentCompatible(*expr.type) ||
           (targetType.isString() && expr.isImplicitString()) ||
           (targetType.isEnum() && isSameEnum(expr, targetType)));
    ASSERT(!targetType.isEquivalent(*expr.type));

    Expression* result = &expr;
    selfDetermined(context, result);
    return *context.scope.getCompilation().emplace<ConversionExpression>(targetType, true, *result,
                                                                         result->sourceRange);
}

Expression& Expression::convertAssignment(const BindContext& context, const Type& type,
                                          Expression& expr, SourceLocation location,
                                          optional<SourceRange> lhsRange) {
    if (expr.bad())
        return expr;

    Compilation& compilation = context.scope.getCompilation();
    if (type.isError())
        return badExpr(compilation, &expr);

    const Type* rt = expr.type;
    if (!type.isAssignmentCompatible(*rt)) {
        // String literals have a type of integer, but are allowed to implicitly convert to the
        // string type. See comments on isSameEnum for why that's here as well.
        if ((type.isString() && expr.isImplicitString()) ||
            (type.isEnum() && isSameEnum(expr, type))) {

            Expression* result = &expr;
            result = &implicitConversion(context, type, *result);
            selfDetermined(context, result);
            return *result;
        }

        DiagCode code =
            type.isCastCompatible(*rt) ? diag::NoImplicitConversion : diag::BadAssignment;
        auto& diag = context.addDiag(code, location);
        diag << *rt << type;
        if (lhsRange)
            diag << *lhsRange;

        diag << expr.sourceRange;
        return badExpr(compilation, &expr);
    }

    Expression* result = &expr;
    if (type.isEquivalent(*rt)) {
        selfDetermined(context, result);
        return *result;
    }

    if (type.isNumeric() && rt->isNumeric()) {
        if ((context.flags & BindFlags::EnumInitializer) != 0 &&
            !checkEnumInitializer(context, type, *result)) {

            return badExpr(compilation, &expr);
        }

        rt = binaryOperatorType(compilation, &type, rt, false);
        contextDetermined(context, result, *rt);

        if (type.isEquivalent(*rt))
            return *result;

        result =
            compilation.emplace<ConversionExpression>(type, true, *result, result->sourceRange);
    }
    else {
        result = &implicitConversion(context, type, *result);
    }

    selfDetermined(context, result);
    return *result;
}

Expression& Expression::badExpr(Compilation& compilation, const Expression* expr) {
    return *compilation.emplace<InvalidExpression>(expr, compilation.getErrorType());
}

void InvalidExpression::toJson(json& j) const {
    if (child)
        j["child"] = *child;
}

IntegerLiteral::IntegerLiteral(BumpAllocator& alloc, const Type& type, const SVInt& value,
                               bool isDeclaredUnsized, SourceRange sourceRange) :
    Expression(ExpressionKind::IntegerLiteral, type, sourceRange),
    isDeclaredUnsized(isDeclaredUnsized),
    valueStorage(value.getBitWidth(), value.isSigned(), value.hasUnknown()) {

    if (value.isSingleWord())
        valueStorage.val = *value.getRawPtr();
    else {
        valueStorage.pVal =
            (uint64_t*)alloc.allocate(sizeof(uint64_t) * value.getNumWords(), alignof(uint64_t));
        memcpy(valueStorage.pVal, value.getRawPtr(), sizeof(uint64_t) * value.getNumWords());
    }
}

Expression& IntegerLiteral::fromSyntax(Compilation& compilation,
                                       const LiteralExpressionSyntax& syntax) {
    ASSERT(syntax.kind == SyntaxKind::IntegerLiteralExpression);

    SVInt val = syntax.literal.intValue().resize(32);
    val.setSigned(true);

    return *compilation.emplace<IntegerLiteral>(compilation, compilation.getIntType(),
                                                std::move(val), true, syntax.sourceRange());
}

Expression& IntegerLiteral::fromSyntax(Compilation& compilation,
                                       const IntegerVectorExpressionSyntax& syntax) {
    const SVInt& value = syntax.value.intValue();

    bitmask<IntegralFlags> flags;
    if (value.isSigned())
        flags |= IntegralFlags::Signed;
    if (value.hasUnknown())
        flags |= IntegralFlags::FourState;

    const Type& type = compilation.getType(value.getBitWidth(), flags);
    return *compilation.emplace<IntegerLiteral>(compilation, type, value, !syntax.size.valid(),
                                                syntax.sourceRange());
}

Expression& RealLiteral::fromSyntax(Compilation& compilation,
                                    const LiteralExpressionSyntax& syntax) {
    ASSERT(syntax.kind == SyntaxKind::RealLiteralExpression);

    return *compilation.emplace<RealLiteral>(compilation.getRealType(), syntax.literal.realValue(),
                                             syntax.sourceRange());
}

Expression& UnbasedUnsizedIntegerLiteral::fromSyntax(Compilation& compilation,
                                                     const LiteralExpressionSyntax& syntax) {
    ASSERT(syntax.kind == SyntaxKind::UnbasedUnsizedLiteralExpression);

    // UnsizedUnbasedLiteralExpressions default to a size of 1 in an undetermined
    // context, but can grow to be wider during propagation.
    logic_t val = syntax.literal.bitValue();
    return *compilation.emplace<UnbasedUnsizedIntegerLiteral>(
        compilation.getType(1,
                            val.isUnknown() ? IntegralFlags::FourState : IntegralFlags::TwoState),
        val, syntax.sourceRange());
}

bool UnbasedUnsizedIntegerLiteral::propagateType(const BindContext&, const Type& newType) {
    bitwidth_t newWidth = newType.getBitWidth();
    ASSERT(newType.isIntegral());
    ASSERT(newWidth);

    type = &newType;
    return true;
}

Expression& NullLiteral::fromSyntax(Compilation& compilation,
                                    const LiteralExpressionSyntax& syntax) {
    ASSERT(syntax.kind == SyntaxKind::NullLiteralExpression);
    return *compilation.emplace<NullLiteral>(compilation.getNullType(), syntax.sourceRange());
}

StringLiteral::StringLiteral(const Type& type, string_view value, string_view rawValue,
                             ConstantValue& intVal, SourceRange sourceRange) :
    Expression(ExpressionKind::StringLiteral, type, sourceRange),
    value(value), rawValue(rawValue), intStorage(&intVal) {
}

Expression& StringLiteral::fromSyntax(Compilation& compilation,
                                      const LiteralExpressionSyntax& syntax) {
    ASSERT(syntax.kind == SyntaxKind::StringLiteralExpression);

    string_view value = syntax.literal.valueText();
    bitwidth_t width;
    ConstantValue* intVal;

    if (value.empty()) {
        // [11.10.3] says that empty string literals take on a value of "\0" (8 zero bits).
        width = 8;
        intVal = compilation.allocConstant(SVInt(8, 0, false));
    }
    else {
        width = bitwidth_t(value.size()) * 8;

        // String literals represented as integers put the first character on the
        // left, which translates to the msb, so we have to reverse the string.
        SmallVectorSized<byte, 64> bytes;
        for (char c : make_reverse_range(value))
            bytes.append((byte)c);

        intVal = compilation.allocConstant(SVInt(width, bytes, false));
    }

    auto& type = compilation.getType(width, IntegralFlags::Unsigned);
    return *compilation.emplace<StringLiteral>(type, value, syntax.literal.rawText(), *intVal,
                                               syntax.sourceRange());
}

void StringLiteral::toJson(json& j) const {
    j["literal"] = value;
}

Expression& NamedValueExpression::fromSymbol(const Scope& scope, const Symbol& symbol,
                                             bool isHierarchical, SourceRange sourceRange) {
    Compilation& compilation = scope.getCompilation();
    if (!symbol.isValue()) {
        scope.addDiag(diag::NotAValue, sourceRange) << symbol.name;
        return badExpr(compilation, nullptr);
    }

    return *compilation.emplace<NamedValueExpression>(symbol.as<ValueSymbol>(), isHierarchical,
                                                      sourceRange);
}

void NamedValueExpression::toJson(json& j) const {
    j["symbol"] = Symbol::jsonLink(symbol);
    j["isHierarchical"] = isHierarchical;
}

Expression& UnaryExpression::fromSyntax(Compilation& compilation,
                                        const PrefixUnaryExpressionSyntax& syntax,
                                        const BindContext& context) {
    Expression& operand = create(compilation, *syntax.operand, context);
    const Type* type = operand.type;

    auto result = compilation.emplace<UnaryExpression>(getUnaryOperator(syntax.kind), *type,
                                                       operand, syntax.sourceRange());
    if (operand.bad())
        return badExpr(compilation, result);

    context.addAttributes(*result, syntax.attributes);

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
            result->type =
                type->isFourState() ? &compilation.getLogicType() : &compilation.getBitType();
            selfDetermined(context, result->operand_);
            break;
        case SyntaxKind::UnaryBitwiseNotExpression:
            // Supported for integral only. Result type is always a single bit.
            good = type->isIntegral();
            result->type =
                type->isFourState() ? &compilation.getLogicType() : &compilation.getBitType();
            break;
        case SyntaxKind::UnaryBitwiseAndExpression:
        case SyntaxKind::UnaryBitwiseOrExpression:
        case SyntaxKind::UnaryBitwiseXorExpression:
        case SyntaxKind::UnaryBitwiseNandExpression:
        case SyntaxKind::UnaryBitwiseNorExpression:
        case SyntaxKind::UnaryBitwiseXnorExpression:
            // Supported for integral only. Result type is always a single bit.
            good = type->isIntegral();
            result->type =
                type->isFourState() ? &compilation.getLogicType() : &compilation.getBitType();
            selfDetermined(context, result->operand_);
            break;
        case SyntaxKind::UnaryPreincrementExpression:
        case SyntaxKind::UnaryPredecrementExpression:
            // Supported for both integral and real types. Result is same as input type.
            // The operand must also be an assignable lvalue.
            // TODO: detect and warn for multiple reads and writes of a single variable in an
            // expression
            // TODO: make sure modifications allowed in this expression
            good = type->isNumeric();
            result->type = type;
            if (!context.requireLValue(operand, syntax.operatorToken.location()))
                return badExpr(compilation, result);
            break;
        default:
            THROW_UNREACHABLE;
    }

    if (!good) {
        auto& diag = context.addDiag(diag::BadUnaryExpression, syntax.operatorToken.location());
        diag << *type;
        diag << operand.sourceRange;
        return badExpr(compilation, result);
    }

    return *result;
}

Expression& UnaryExpression::fromSyntax(Compilation& compilation,
                                        const PostfixUnaryExpressionSyntax& syntax,
                                        const BindContext& context) {
    Expression& operand = create(compilation, *syntax.operand, context);
    const Type* type = operand.type;

    // This method is only ever called for postincrement and postdecrement operators, so
    // the operand must be an lvalue.
    Expression* result = compilation.emplace<UnaryExpression>(getUnaryOperator(syntax.kind), *type,
                                                              operand, syntax.sourceRange());
    if (operand.bad() || !context.requireLValue(operand, syntax.operatorToken.location()))
        return badExpr(compilation, result);

    if (!type->isNumeric()) {
        auto& diag = context.addDiag(diag::BadUnaryExpression, syntax.operatorToken.location());
        diag << *type;
        diag << operand.sourceRange;
        return badExpr(compilation, result);
    }

    context.addAttributes(*result, syntax.attributes);
    return *result;
}

bool UnaryExpression::propagateType(const BindContext& context, const Type& newType) {
    switch (op) {
        case UnaryOperator::Plus:
        case UnaryOperator::Minus:
        case UnaryOperator::BitwiseNot:
            type = &newType;
            contextDetermined(context, operand_, newType);
            return true;
        case UnaryOperator::BitwiseAnd:
        case UnaryOperator::BitwiseOr:
        case UnaryOperator::BitwiseXor:
        case UnaryOperator::BitwiseNand:
        case UnaryOperator::BitwiseNor:
        case UnaryOperator::BitwiseXnor:
        case UnaryOperator::LogicalNot:
        case UnaryOperator::Preincrement:
        case UnaryOperator::Predecrement:
        case UnaryOperator::Postincrement:
        case UnaryOperator::Postdecrement:
            // Operand is self determined and already folded.
            return false;
    }
    THROW_UNREACHABLE;
}

void UnaryExpression::toJson(json& j) const {
    j["op"] = toString(op);
    j["operand"] = operand();
}

Expression& BinaryExpression::fromSyntax(Compilation& compilation,
                                         const BinaryExpressionSyntax& syntax,
                                         const BindContext& context) {
    Expression& lhs = create(compilation, *syntax.left, context);
    Expression& rhs = create(compilation, *syntax.right, context);
    const Type* lt = lhs.type;
    const Type* rt = rhs.type;

    auto result = compilation.emplace<BinaryExpression>(getBinaryOperator(syntax.kind), *lhs.type,
                                                        lhs, rhs, syntax.sourceRange());
    if (lhs.bad() || rhs.bad())
        return badExpr(compilation, result);

    bool bothIntegral = lt->isIntegral() && rt->isIntegral();
    bool bothNumeric = lt->isNumeric() && rt->isNumeric();
    bool bothStrings = lhs.isImplicitString() && rhs.isImplicitString();

    bool good;
    switch (syntax.kind) {
        case SyntaxKind::AddExpression:
        case SyntaxKind::SubtractExpression:
        case SyntaxKind::MultiplyExpression:
            good = bothNumeric;
            result->type = binaryOperatorType(compilation, lt, rt, false);
            break;
        case SyntaxKind::DivideExpression:
            // Result is forced to 4-state because result can be X.
            good = bothNumeric;
            result->type = binaryOperatorType(compilation, lt, rt, true);
            break;
        case SyntaxKind::ModExpression:
            // Result is forced to 4-state because result can be X.
            // Different from divide because only integers are allowed.
            good = bothIntegral;
            result->type = binaryOperatorType(compilation, lt, rt, true);
            break;
        case SyntaxKind::BinaryAndExpression:
        case SyntaxKind::BinaryOrExpression:
        case SyntaxKind::BinaryXorExpression:
        case SyntaxKind::BinaryXnorExpression:
            good = bothIntegral;
            result->type = binaryOperatorType(compilation, lt, rt, false);
            break;
        case SyntaxKind::LogicalShiftLeftExpression:
        case SyntaxKind::LogicalShiftRightExpression:
        case SyntaxKind::ArithmeticShiftLeftExpression:
        case SyntaxKind::ArithmeticShiftRightExpression:
            // The result is always the same type as the lhs, except that if the rhs is
            // four state then the lhs also becomes four state.
            good = bothIntegral;
            if (rt->isFourState())
                result->type = forceFourState(compilation, lt);
            else
                result->type = lt;
            selfDetermined(context, result->right_);
            break;
        case SyntaxKind::PowerExpression:
            good = bothNumeric;
            if (lt->isFloating() || rt->isFloating()) {
                result->type = binaryOperatorType(compilation, lt, rt, false);
                contextDetermined(context, result->right_, *result->type);
            }
            else {
                // Result is forced to 4-state because result can be X.
                result->type = forceFourState(compilation, lt);
                selfDetermined(context, result->right_);
            }
            break;
        case SyntaxKind::GreaterThanEqualExpression:
        case SyntaxKind::GreaterThanExpression:
        case SyntaxKind::LessThanEqualExpression:
        case SyntaxKind::LessThanExpression: {
            // Result is always a single bit.
            good = bothNumeric || bothStrings;
            result->type = singleBitType(compilation, lt, rt);

            // Result type is fixed but the two operands affect each other as they would in
            // other context-determined operators.
            auto nt = (good && !bothNumeric) ? &compilation.getStringType()
                                             : binaryOperatorType(compilation, lt, rt, false);
            contextDetermined(context, result->left_, *nt);
            contextDetermined(context, result->right_, *nt);
            break;
        }
        case SyntaxKind::LogicalAndExpression:
        case SyntaxKind::LogicalOrExpression:
        case SyntaxKind::LogicalImplicationExpression:
        case SyntaxKind::LogicalEquivalenceExpression:
            // Result is always a single bit.
            good = bothNumeric;
            result->type = singleBitType(compilation, lt, rt);
            selfDetermined(context, result->left_);
            selfDetermined(context, result->right_);
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
                // For equality and inequality, result is four state if either operand is
                // four state. For case equality and case inequality, result is never four
                // state. For wildcard equality / inequality, result is four state only if
                // lhs is four state.
                if (syntax.kind == SyntaxKind::EqualityExpression ||
                    syntax.kind == SyntaxKind::InequalityExpression) {
                    good = true;
                    result->type = singleBitType(compilation, lt, rt);
                }
                else if (syntax.kind == SyntaxKind::CaseEqualityExpression ||
                         syntax.kind == SyntaxKind::CaseInequalityExpression) {
                    good = true;
                    result->type = &compilation.getBitType();
                }
                else {
                    good = bothIntegral;
                    result->type =
                        lt->isFourState() ? &compilation.getLogicType() : &compilation.getBitType();
                }

                // Result type is fixed but the two operands affect each other as they would
                // in other context-determined operators.
                auto nt = binaryOperatorType(compilation, lt, rt, false);
                contextDetermined(context, result->left_, *nt);
                contextDetermined(context, result->right_, *nt);
            }
            else {
                bool isContext = false;
                bool isWildcard = syntax.kind == SyntaxKind::WildcardEqualityExpression ||
                                  syntax.kind == SyntaxKind::WildcardInequalityExpression;

                if (bothStrings) {
                    good = !isWildcard;
                    result->type = &compilation.getBitType();

                    // If there is a literal involved, make sure it's converted to string.
                    isContext = true;
                    contextDetermined(context, result->left_, compilation.getStringType());
                    contextDetermined(context, result->right_, compilation.getStringType());
                }
                else if (lt->isAggregate() && lt->isEquivalent(*rt)) {
                    good = !isWildcard;
                    result->type = singleBitType(compilation, lt, rt);
                }
                else if ((lt->isClass() && lt->isAssignmentCompatible(*rt)) ||
                         (rt->isClass() && rt->isAssignmentCompatible(*lt))) {
                    good = true;
                    result->type = &compilation.getBitType();
                }
                else if ((lt->isCHandle() || lt->isNull()) && (rt->isCHandle() || rt->isNull())) {
                    good = true;
                    result->type = &compilation.getBitType();
                }
                else {
                    good = false;
                }

                if (!isContext) {
                    selfDetermined(context, result->left_);
                    selfDetermined(context, result->right_);
                }
            }
            break;
        default:
            THROW_UNREACHABLE;
    }

    auto location = syntax.operatorToken.location();
    if (!good) {
        auto& diag = context.addDiag(diag::BadBinaryExpression, location);
        diag << *lt << *rt;
        diag << lhs.sourceRange;
        diag << rhs.sourceRange;
        return badExpr(compilation, result);
    }

    context.addAttributes(*result, syntax.attributes);
    return *result;
}

bool BinaryExpression::propagateType(const BindContext& context, const Type& newType) {
    switch (op) {
        case BinaryOperator::Add:
        case BinaryOperator::Subtract:
        case BinaryOperator::Multiply:
        case BinaryOperator::Divide:
        case BinaryOperator::Mod:
        case BinaryOperator::BinaryAnd:
        case BinaryOperator::BinaryOr:
        case BinaryOperator::BinaryXor:
        case BinaryOperator::BinaryXnor:
            type = &newType;
            contextDetermined(context, left_, newType);
            contextDetermined(context, right_, newType);
            return true;
        case BinaryOperator::Equality:
        case BinaryOperator::Inequality:
        case BinaryOperator::CaseEquality:
        case BinaryOperator::CaseInequality:
        case BinaryOperator::GreaterThanEqual:
        case BinaryOperator::GreaterThan:
        case BinaryOperator::LessThanEqual:
        case BinaryOperator::LessThan:
        case BinaryOperator::WildcardEquality:
        case BinaryOperator::WildcardInequality:
        case BinaryOperator::LogicalAnd:
        case BinaryOperator::LogicalOr:
        case BinaryOperator::LogicalImplication:
        case BinaryOperator::LogicalEquivalence:
            // Type is already set (always 1 bit) and operands are already folded.
            return false;
        case BinaryOperator::LogicalShiftLeft:
        case BinaryOperator::LogicalShiftRight:
        case BinaryOperator::ArithmeticShiftLeft:
        case BinaryOperator::ArithmeticShiftRight:
        case BinaryOperator::Power:
            // Only the left hand side gets propagated; the rhs is self determined.
            type = &newType;
            contextDetermined(context, left_, newType);
            return true;
    }
    THROW_UNREACHABLE;
}

void BinaryExpression::toJson(json& j) const {
    j["op"] = toString(op);
    j["left"] = left();
    j["right"] = right();
}

Expression& ConditionalExpression::fromSyntax(Compilation& compilation,
                                              const ConditionalExpressionSyntax& syntax,
                                              const BindContext& context,
                                              const Type* assignmentTarget) {
    if (syntax.predicate->conditions.size() != 1) {
        context.addDiag(diag::NotYetSupported, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    auto& pred = selfDetermined(compilation, *syntax.predicate->conditions[0]->expr, context);

    // If the predicate is known at compile time, we can tell which branch will be unevaluated.
    BindFlags leftFlags = BindFlags::None;
    BindFlags rightFlags = BindFlags::None;
    if (pred.constant && (!pred.constant->isInteger() || !pred.constant->integer().hasUnknown())) {
        if (pred.constant->isTrue())
            rightFlags = BindFlags::UnevaluatedBranch;
        else
            leftFlags = BindFlags::UnevaluatedBranch;
    }

    auto& left = create(compilation, *syntax.left, context, leftFlags, assignmentTarget);
    auto& right = create(compilation, *syntax.right, context, rightFlags, assignmentTarget);

    // Force four-state return type for ambiguous condition case.
    const Type* resultType =
        binaryOperatorType(compilation, left.type, right.type, pred.type->isFourState());
    auto result = compilation.emplace<ConditionalExpression>(*resultType, pred, left, right,
                                                             syntax.sourceRange());
    if (pred.bad() || left.bad() || right.bad())
        return badExpr(compilation, result);

    if (!context.requireBooleanConvertible(pred))
        return badExpr(compilation, result);

    // If both sides of the expression are numeric, we've already determined the correct
    // result type. Otherwise, follow the rules in [11.14.11].
    bool good = true;
    const Type& lt = *left.type;
    const Type& rt = *right.type;
    if (!lt.isNumeric() || !rt.isNumeric()) {
        if (lt.isNull() && rt.isNull()) {
            result->type = &compilation.getNullType();
        }
        else if (lt.isClass() || rt.isClass()) {
            if (lt.isNull())
                result->type = &rt;
            else if (rt.isNull())
                result->type = &lt;
            else if (rt.isAssignmentCompatible(lt))
                result->type = &rt;
            else if (lt.isAssignmentCompatible(rt))
                result->type = &lt;
            // TODO: handle case for class types derived from common base
            else if (lt.isEquivalent(rt))
                result->type = &lt;
            else
                good = false;
        }
        else if (lt.isEquivalent(rt)) {
            result->type = &lt;
        }
        else if (left.isImplicitString() && right.isImplicitString()) {
            result->type = &compilation.getStringType();
        }
        else {
            good = false;
        }
    }

    if (!good) {
        auto& diag = context.addDiag(diag::BadConditionalExpression, syntax.question.location());
        diag << lt << rt;
        diag << left.sourceRange;
        diag << right.sourceRange;
        return badExpr(compilation, result);
    }

    context.addAttributes(*result, syntax.attributes);
    return *result;
}

bool ConditionalExpression::propagateType(const BindContext& context, const Type& newType) {
    // The predicate is self determined so no need to handle it here.
    type = &newType;
    contextDetermined(context, left_, newType);
    contextDetermined(context, right_, newType);
    return true;
}

void ConditionalExpression::toJson(json& j) const {
    j["pred"] = pred();
    j["left"] = left();
    j["right"] = right();
}

Expression& AssignmentExpression::fromSyntax(Compilation& compilation,
                                             const BinaryExpressionSyntax& syntax,
                                             const BindContext& context) {
    // TODO: verify that assignment is allowed in this expression context
    auto op = syntax.kind == SyntaxKind::AssignmentExpression
                  ? std::nullopt
                  : std::make_optional(getBinaryOperator(syntax.kind));

    // The right hand side of an assignment expression is typically an
    // "assignment-like context", except if the left hand side does not
    // have a self-determined type. That can only be true if the lhs is
    // an assignment pattern without an explicit type.
    if (syntax.left->kind == SyntaxKind::AssignmentPatternExpression) {
        auto& pattern = syntax.left->as<AssignmentPatternExpressionSyntax>();
        if (!pattern.type) {
            // In this case we have to bind the rhs first to determine the
            // correct type to use as the context for the lhs.
            Expression* rhs = &selfDetermined(compilation, *syntax.right, context);
            if (rhs->bad())
                return badExpr(compilation, rhs);

            Expression* lhs =
                &create(compilation, *syntax.left, context, BindFlags::None, rhs->type);
            selfDetermined(context, lhs);

            auto result = compilation.emplace<AssignmentExpression>(op, *lhs->type, *lhs, *rhs,
                                                                    syntax.sourceRange());
            if (rhs->bad())
                return badExpr(compilation, result);

            return *result;
        }
    }

    Expression& lhs = selfDetermined(compilation, *syntax.left, context);
    Expression& rhs = create(compilation, *syntax.right, context);

    auto result =
        compilation.emplace<AssignmentExpression>(op, *lhs.type, lhs, rhs, syntax.sourceRange());
    if (lhs.bad() || rhs.bad())
        return badExpr(compilation, result);

    // Make sure we can actually assign to the thing on the lhs.
    // TODO: check for const assignment
    auto location = syntax.operatorToken.location();
    if (!context.requireLValue(lhs, location))
        return badExpr(compilation, result);

    result->right_ =
        &convertAssignment(context, *lhs.type, *result->right_, location, lhs.sourceRange);
    if (result->right_->bad())
        return badExpr(compilation, result);

    return *result;
}

void AssignmentExpression::toJson(json& j) const {
    j["left"] = left();
    j["right"] = right();

    if (op)
        j["op"] = toString(*op);
}

Expression& ElementSelectExpression::fromSyntax(Compilation& compilation, Expression& value,
                                                const ExpressionSyntax& syntax,
                                                SourceRange fullRange, const BindContext& context) {
    Expression& selector = selfDetermined(compilation, syntax, context);
    const Type& resultType = getIndexedType(compilation, context, *value.type, syntax.sourceRange(),
                                            value.sourceRange, false);

    auto result =
        compilation.emplace<ElementSelectExpression>(resultType, value, selector, fullRange);
    if (value.bad() || selector.bad() || result->bad())
        return badExpr(compilation, result);

    if (!selector.type->isIntegral()) {
        context.addDiag(diag::ExprMustBeIntegral, selector.sourceRange);
        return badExpr(compilation, result);
    }

    // If the selector is constant, we can do checking at compile time that it's within bounds.
    // Only do that if we're not in an unevaluated conditional branch.
    if (selector.constant && (context.flags & BindFlags::UnevaluatedBranch) == 0) {
        optional<int32_t> index = selector.constant->integer().as<int32_t>();
        if (!index || !value.type->getArrayRange().containsPoint(*index)) {
            auto& diag = context.addDiag(diag::IndexValueInvalid, selector.sourceRange);
            diag << *selector.constant;
            diag << *value.type;
            return badExpr(compilation, result);
        }
    }

    return *result;
}

void ElementSelectExpression::toJson(json& j) const {
    j["value"] = value();
    j["selector"] = selector();
}

Expression& RangeSelectExpression::fromSyntax(Compilation& compilation, Expression& value,
                                              const RangeSelectSyntax& syntax,
                                              SourceRange fullRange, const BindContext& context) {
    // Left and right are either the extents of a part-select, in which case they must
    // both be constant, or the left hand side is the start and the right hand side is
    // the width of an indexed part select, in which case only the rhs need be constant.
    RangeSelectionKind selectionKind;
    switch (syntax.kind) {
        case SyntaxKind::SimpleRangeSelect:
            selectionKind = RangeSelectionKind::Simple;
            break;
        case SyntaxKind::AscendingRangeSelect:
            selectionKind = RangeSelectionKind::IndexedUp;
            break;
        case SyntaxKind::DescendingRangeSelect:
            selectionKind = RangeSelectionKind::IndexedDown;
            break;
        default:
            THROW_UNREACHABLE;
    }

    const Expression& left = selectionKind == RangeSelectionKind::Simple
                                 ? bind(*syntax.left, context, BindFlags::Constant)
                                 : selfDetermined(compilation, *syntax.left, context);

    const Expression& right = bind(*syntax.right, context, BindFlags::Constant);

    auto result = compilation.emplace<RangeSelectExpression>(
        selectionKind, compilation.getErrorType(), value, left, right, fullRange);

    if (value.bad() || left.bad() || right.bad())
        return badExpr(compilation, result);

    if (!left.type->isIntegral()) {
        context.addDiag(diag::ExprMustBeIntegral, left.sourceRange);
        return badExpr(compilation, result);
    }
    if (!right.type->isIntegral()) {
        context.addDiag(diag::ExprMustBeIntegral, right.sourceRange);
        return badExpr(compilation, result);
    }

    const Type& elementType = getIndexedType(compilation, context, *value.type,
                                             syntax.sourceRange(), value.sourceRange, true);
    if (elementType.isError())
        return badExpr(compilation, result);

    // As mentioned, rhs must always be a constant integer.
    optional<int32_t> rv = context.evalInteger(right);
    if (!rv)
        return badExpr(compilation, result);

    ConstantRange selectionRange;
    ConstantRange valueRange = value.type->getArrayRange();
    SourceRange errorRange{ left.sourceRange.start(), right.sourceRange.end() };

    // Helper function for validating the bounds of the selection.
    auto validateRange = [&](auto range) {
        if (!valueRange.containsPoint(range.left) || !valueRange.containsPoint(range.right)) {
            auto& diag = context.addDiag(diag::BadRangeExpression, errorRange);
            diag << range.left << range.right;
            diag << *value.type;
            return false;
        }
        return true;
    };

    if (selectionKind == RangeSelectionKind::Simple) {
        optional<int32_t> lv = context.evalInteger(left);
        if (!lv)
            return badExpr(compilation, result);

        selectionRange = { *lv, *rv };
        if (selectionRange.isLittleEndian() != valueRange.isLittleEndian()) {
            auto& diag = context.addDiag(diag::SelectEndianMismatch, errorRange);
            diag << *value.type;
            return badExpr(compilation, result);
        }

        if ((context.flags & BindFlags::UnevaluatedBranch) == 0 && !validateRange(selectionRange))
            return badExpr(compilation, result);
    }
    else {
        if (!context.requireGtZero(rv, right.sourceRange))
            return badExpr(compilation, result);

        if (bitwidth_t(*rv) > valueRange.width()) {
            auto& diag = context.addDiag(diag::RangeWidthTooLarge, right.sourceRange);
            diag << *rv;
            diag << *value.type;
            return badExpr(compilation, result);
        }

        // If the lhs is a known constant, we can check that now too.
        if (left.constant && (context.flags & BindFlags::UnevaluatedBranch) == 0) {
            optional<int32_t> index = left.constant->integer().as<int32_t>();
            if (!index) {
                auto& diag = context.addDiag(diag::IndexValueInvalid, left.sourceRange);
                diag << *left.constant;
                diag << *value.type;
                return badExpr(compilation, result);
            }

            selectionRange =
                getIndexedRange(selectionKind, *index, *rv, valueRange.isLittleEndian());

            if (!validateRange(selectionRange))
                return badExpr(compilation, result);
        }
        else {
            // Otherwise, the resulting range will start with the fixed lower bound of the type.
            int32_t count = *rv - 1;
            if (selectionKind == RangeSelectionKind::IndexedUp) {
                selectionRange.left = valueRange.lower() + count;
                selectionRange.right = valueRange.lower();
            }
            else {
                selectionRange.left = valueRange.upper();
                selectionRange.right = valueRange.upper() - count;
            }

            if (!valueRange.isLittleEndian())
                selectionRange.reverse();
        }
    }

    // At this point, all expressions are good, ranges have been validated and
    // we know the final width of the selection, so pick the result type and we're done.
    if (value.type->isUnpackedArray())
        result->type = compilation.emplace<UnpackedArrayType>(elementType, selectionRange);
    else
        result->type = compilation.emplace<PackedArrayType>(elementType, selectionRange);

    return *result;
}

ConstantRange RangeSelectExpression::getIndexedRange(RangeSelectionKind kind, int32_t l, int32_t r,
                                                     bool littleEndian) {
    // TODO: avoid overflow
    ConstantRange result;
    int32_t count = r - 1;
    if (kind == RangeSelectionKind::IndexedUp) {
        result.left = l + count;
        result.right = l;
    }
    else {
        result.left = l;
        result.right = l - count;
    }

    if (!littleEndian)
        result.reverse();

    return result;
}

void RangeSelectExpression::toJson(json& j) const {
    j["selectionKind"] = toString(selectionKind);
    j["value"] = value();
    j["left"] = left();
    j["right"] = right();
}

Expression& MemberAccessExpression::fromSelector(Compilation& compilation, Expression& expr,
                                                 const LookupResult::MemberSelector& selector,
                                                 const InvocationExpressionSyntax* invocation,
                                                 const BindContext& context) {
    // This might look like a member access but actually be a built-in type method.
    const Type& type = expr.type->getCanonicalType();
    switch (type.kind) {
        case SymbolKind::PackedStructType:
        case SymbolKind::UnpackedStructType:
        case SymbolKind::PackedUnionType:
        case SymbolKind::UnpackedUnionType:
            break;
        case SymbolKind::EnumType:
        case SymbolKind::StringType:
        case SymbolKind::UnpackedArrayType:
            return CallExpression::fromSystemMethod(compilation, expr, selector, invocation,
                                                    context);
        default: {
            auto& diag = context.addDiag(diag::InvalidMemberAccess, selector.dotLocation);
            diag << expr.sourceRange;
            diag << selector.nameRange;
            diag << *expr.type;
            return badExpr(compilation, &expr);
        }
    }

    const Symbol* member = expr.type->getCanonicalType().as<Scope>().find(selector.name);
    if (!member) {
        auto& diag = context.addDiag(diag::UnknownMember, selector.nameRange.start());
        diag << expr.sourceRange;
        diag << selector.name;
        diag << *expr.type;
        return badExpr(compilation, &expr);
    }

    // The source range of the entire member access starts from the value being selected.
    SourceRange range{ expr.sourceRange.start(), selector.nameRange.end() };
    const auto& field = member->as<FieldSymbol>();
    return *compilation.emplace<MemberAccessExpression>(field.getType(), expr, field, range);
}

Expression& MemberAccessExpression::fromSyntax(Compilation& compilation,
                                               const MemberAccessExpressionSyntax& syntax,
                                               const InvocationExpressionSyntax* invocation,
                                               const BindContext& context) {
    auto name = syntax.name.valueText();
    Expression& lhs = selfDetermined(compilation, *syntax.left, context);
    if (lhs.bad() || name.empty())
        return badExpr(compilation, &lhs);

    LookupResult::MemberSelector selector;
    selector.name = name;
    selector.dotLocation = syntax.dot.location();
    selector.nameRange = syntax.name.range();
    return fromSelector(compilation, lhs, selector, invocation, context);
}

void MemberAccessExpression::toJson(json& j) const {
    j["field"] = Symbol::jsonLink(field);
    j["value"] = value();
}

Expression& ConcatenationExpression::fromSyntax(Compilation& compilation,
                                                const ConcatenationExpressionSyntax& syntax,
                                                const BindContext& context) {
    bool errored = false;
    bool anyStrings = false;
    bitmask<IntegralFlags> flags;
    bitwidth_t totalWidth = 0;
    SmallVectorSized<Expression*, 8> buffer;

    for (auto argSyntax : syntax.expressions) {
        // Replications inside of concatenations have a special feature that allows them to have
        // a width of zero. Check now if we're going to be binding a replication and if so set
        // an additional flag so that it knows it's ok to have that zero count.
        Expression* arg;
        if (argSyntax->kind == SyntaxKind::MultipleConcatenationExpression)
            arg = &create(compilation, *argSyntax, context, BindFlags::InsideConcatenation);
        else
            arg = &create(compilation, *argSyntax, context);
        buffer.append(arg);

        if (arg->bad()) {
            errored = true;
            break;
        }

        const Type& type = *arg->type;
        if (type.isVoid() && argSyntax->kind == SyntaxKind::MultipleConcatenationExpression)
            continue;

        if (type.isString()) {
            anyStrings = true;
            continue;
        }

        if (!type.isIntegral()) {
            errored = true;
            context.addDiag(diag::BadConcatExpression, arg->sourceRange) << type;
            break;
        }

        // Can't overflow because 2*maxWidth is still less than 2^32-1.
        totalWidth += type.getBitWidth();

        if (!context.requireValidBitWidth(totalWidth, syntax.sourceRange())) {
            errored = true;
            break;
        }

        if (type.isFourState())
            flags |= IntegralFlags::FourState;
    }

    if (!errored) {
        for (size_t i = 0; i < buffer.size(); i++) {
            if (!anyStrings)
                selfDetermined(context, buffer[i]);
            else {
                Expression* expr = buffer[i];
                if (expr->type->isString())
                    selfDetermined(context, expr);
                else if (expr->isImplicitString())
                    contextDetermined(context, expr, compilation.getStringType());
                else {
                    errored = true;
                    context.addDiag(diag::ConcatWithStringInt, expr->sourceRange);
                    break;
                }
                buffer[i] = expr;
            }
        }
    }

    if (errored) {
        return badExpr(compilation, compilation.emplace<ConcatenationExpression>(
                                        compilation.getErrorType(), span<const Expression*>(),
                                        syntax.sourceRange()));
    }

    const Type* type;
    if (anyStrings)
        type = &compilation.getStringType();
    else
        type = &compilation.getType(totalWidth, flags);

    // TODO: Workaround GCC bugs
    auto copied = buffer.copy(compilation);
    span<const Expression* const> elements(copied.data(), copied.size());
    return *compilation.emplace<ConcatenationExpression>(*type, elements, syntax.sourceRange());
}

void ConcatenationExpression::toJson(json& j) const {
    for (auto op : operands())
        j["operands"].push_back(*op);
}

Expression& ReplicationExpression::fromSyntax(Compilation& compilation,
                                              const MultipleConcatenationExpressionSyntax& syntax,
                                              const BindContext& context) {
    Expression& left = selfDetermined(compilation, *syntax.expression, context);
    Expression* right = &create(compilation, *syntax.concatenation, context);

    auto result = compilation.emplace<ReplicationExpression>(compilation.getErrorType(), left,
                                                             *right, syntax.sourceRange());
    if (left.bad() || right->bad())
        return badExpr(compilation, result);

    // TODO: unpacked arrays
    if (!left.type->isIntegral() || (!right->type->isIntegral() && !right->type->isString())) {
        auto& diag = context.addDiag(diag::BadReplicationExpression,
                                     syntax.concatenation->getFirstToken().location());
        diag << *left.type << *right->type;
        diag << left.sourceRange;
        diag << right->sourceRange;
        return badExpr(compilation, result);
    }

    // If the multiplier isn't constant this must be a string replication.
    if (!left.constant) {
        if (!right->isImplicitString()) {
            // They probably meant for this to be a constant (non-string) replication,
            // so do the normal error reporting for that case.
            checkBindFlags(left, context.resetFlags(BindFlags::Constant));
            return badExpr(compilation, result);
        }

        contextDetermined(context, right, compilation.getStringType());

        result->concat_ = right;
        result->type = &compilation.getStringType();
        return *result;
    }

    optional<int32_t> count = context.evalInteger(left);
    if (!count)
        return badExpr(compilation, result);

    if (*count < 0) {
        context.requireGtZero(count, left.sourceRange);
        return badExpr(compilation, result);
    }

    if (*count == 0) {
        if ((context.flags & BindFlags::InsideConcatenation) == 0) {
            context.addDiag(diag::ReplicationZeroOutsideConcat, left.sourceRange);
            return badExpr(compilation, result);
        }

        // Use a placeholder type here to indicate to the parent concatenation that this had a
        // zero width.
        result->type = &compilation.getVoidType();
        return *result;
    }

    selfDetermined(context, right);
    result->concat_ = right;

    if (right->type->isString()) {
        result->type = &compilation.getStringType();
        return *result;
    }

    auto width = context.requireValidBitWidth(
        SVInt(32, uint64_t(*count), true) * right->type->getBitWidth(), syntax.sourceRange());
    if (!width)
        return badExpr(compilation, result);

    result->type = &compilation.getType(
        *width, right->type->isFourState() ? IntegralFlags::FourState : IntegralFlags::TwoState);
    return *result;
}

void ReplicationExpression::toJson(json& j) const {
    j["count"] = count();
    j["concat"] = concat();
}

Expression& CallExpression::fromSyntax(Compilation& compilation,
                                       const InvocationExpressionSyntax& syntax,
                                       const BindContext& context) {
    if (syntax.left->kind == SyntaxKind::MemberAccessExpression) {
        return MemberAccessExpression::fromSyntax(
            compilation, syntax.left->as<MemberAccessExpressionSyntax>(), &syntax, context);
    }

    if (!NameSyntax::isKind(syntax.left->kind)) {
        SourceLocation loc = syntax.arguments ? syntax.arguments->openParen.location()
                                              : syntax.left->getFirstToken().location();
        auto& diag = context.addDiag(diag::ExpressionNotCallable, loc);
        diag << syntax.left->sourceRange();
        return badExpr(compilation, nullptr);
    }

    return bindName(compilation, syntax.left->as<NameSyntax>(), &syntax, context);
}

Expression& CallExpression::fromLookup(Compilation& compilation, const Subroutine& subroutine,
                                       const InvocationExpressionSyntax* syntax, SourceRange range,
                                       const BindContext& context) {

    if (subroutine.index() == 1) {
        const SystemSubroutine& systemSubroutine = *std::get<1>(subroutine);
        return createSystemCall(compilation, systemSubroutine, nullptr, syntax, range, context);
    }

    const SubroutineSymbol& symbol = *std::get<0>(subroutine);

    SmallVectorSized<const Expression*, 8> argBuffer;
    if (syntax && syntax->arguments) {
        auto actualArgs = syntax->arguments->parameters;

        // TODO: handle too few args as well, which requires looking at default values
        auto formalArgs = symbol.arguments;
        if (formalArgs.size() < actualArgs.size()) {
            auto& diag = context.addDiag(diag::TooManyArguments, syntax->left->sourceRange());
            diag << formalArgs.size();
            diag << actualArgs.size();
            return badExpr(compilation, nullptr);
        }

        // TODO: handle named arguments in addition to ordered
        for (size_t i = 0; i < actualArgs.size(); i++) {
            const auto& arg = actualArgs[i]->as<OrderedArgumentSyntax>();
            argBuffer.append(&Expression::bind(formalArgs[i]->getType(), *arg.expr,
                                               arg.getFirstToken().location(), context));
        }
    }

    auto result = compilation.emplace<CallExpression>(&symbol, symbol.getReturnType(),
                                                      argBuffer.copy(compilation),
                                                      context.lookupLocation, range);
    for (auto arg : result->arguments()) {
        if (arg->bad())
            return badExpr(compilation, result);
    }

    if (syntax)
        context.addAttributes(*result, syntax->attributes);

    return *result;
}

Expression& CallExpression::fromSystemMethod(Compilation& compilation, const Expression& expr,
                                             const LookupResult::MemberSelector& selector,
                                             const InvocationExpressionSyntax* syntax,
                                             const BindContext& context) {
    const Type& type = expr.type->getCanonicalType();
    auto subroutine = compilation.getSystemMethod(type.kind, selector.name);
    if (!subroutine) {
        if (syntax) {
            context.addDiag(diag::UnknownSystemMethod, selector.nameRange) << selector.name;
        }
        else {
            auto& diag = context.addDiag(diag::InvalidMemberAccess, selector.dotLocation);
            diag << expr.sourceRange;
            diag << selector.nameRange;
            diag << *expr.type;
        }
        return badExpr(compilation, &expr);
    }

    return createSystemCall(compilation, *subroutine, &expr, syntax,
                            syntax ? syntax->sourceRange() : expr.sourceRange, context);
}

Expression& CallExpression::createSystemCall(Compilation& compilation,
                                             const SystemSubroutine& subroutine,
                                             const Expression* firstArg,
                                             const InvocationExpressionSyntax* syntax,
                                             SourceRange range, const BindContext& context) {
    SmallVectorSized<const Expression*, 8> buffer;
    if (firstArg)
        buffer.append(firstArg);

    if (syntax && syntax->arguments) {
        auto actualArgs = syntax->arguments->parameters;
        for (size_t i = 0; i < actualArgs.size(); i++) {
            // TODO: error if not ordered arguments
            const auto& arg = actualArgs[i]->as<OrderedArgumentSyntax>();
            buffer.append(&subroutine.bindArgument(i, context, *arg.expr));
        }
    }

    const Type& type = subroutine.checkArguments(context, buffer, range);
    auto expr = compilation.emplace<CallExpression>(&subroutine, type, buffer.copy(compilation),
                                                    context.lookupLocation, range);

    if (type.isError())
        return badExpr(compilation, expr);

    for (auto arg : expr->arguments()) {
        if (arg->bad())
            return badExpr(compilation, expr);
    }

    if (syntax)
        context.addAttributes(*expr, syntax->attributes);

    return *expr;
}

void CallExpression::toJson(json& j) const {
    if (subroutine.index() == 1) {
        const SystemSubroutine& systemSubroutine = *std::get<1>(subroutine);
        j["subroutine"] = systemSubroutine.name;
    }
    else {
        const SubroutineSymbol& symbol = *std::get<0>(subroutine);
        j["subroutine"] = Symbol::jsonLink(symbol);

        for (auto arg : arguments())
            j["arguments"].push_back(*arg);
    }
}

Expression& ConversionExpression::fromSyntax(Compilation& compilation,
                                             const CastExpressionSyntax& syntax,
                                             const BindContext& context) {
    auto& targetExpr = bind(*syntax.left, context, BindFlags::AllowDataType | BindFlags::Constant);
    auto& operand = selfDetermined(compilation, *syntax.right, context);

    auto result = compilation.emplace<ConversionExpression>(compilation.getErrorType(), false,
                                                            operand, syntax.sourceRange());
    if (targetExpr.bad() || operand.bad())
        return badExpr(compilation, result);

    if (targetExpr.kind == ExpressionKind::DataType) {
        result->type = targetExpr.type;
    }
    else {
        auto val = context.evalInteger(targetExpr);
        if (!val || !context.requireGtZero(val, targetExpr.sourceRange))
            return badExpr(compilation, result);

        bitwidth_t width = bitwidth_t(*val);
        if (!context.requireValidBitWidth(width, targetExpr.sourceRange))
            return badExpr(compilation, result);

        if (!operand.type->isIntegral()) {
            auto& diag = context.addDiag(diag::BadIntegerCast, syntax.apostrophe.location());
            diag << *operand.type;
            diag << targetExpr.sourceRange << operand.sourceRange;
            return badExpr(compilation, result);
        }

        result->type = &compilation.getType(width, operand.type->getIntegralFlags());
    }

    const Type& type = *result->type;
    if (!type.isCastCompatible(*operand.type)) {
        auto& diag = context.addDiag(diag::BadConversion, syntax.apostrophe.location());
        diag << *operand.type << type;
        diag << targetExpr.sourceRange << operand.sourceRange;
        return badExpr(compilation, result);
    }

    return *result;
}

Expression& ConversionExpression::fromSyntax(Compilation& compilation,
                                             const SignedCastExpressionSyntax& syntax,
                                             const BindContext& context) {
    auto& operand = selfDetermined(compilation, *syntax.inner, context);
    auto result = compilation.emplace<ConversionExpression>(compilation.getErrorType(), false,
                                                            operand, syntax.sourceRange());
    if (operand.bad())
        return badExpr(compilation, result);

    if (!operand.type->isIntegral()) {
        auto& diag = context.addDiag(diag::BadIntegerCast, syntax.apostrophe.location());
        diag << *operand.type;
        diag << operand.sourceRange;
        return badExpr(compilation, result);
    }

    auto flags = operand.type->getIntegralFlags() & ~IntegralFlags::Signed;
    if (syntax.signing.kind == TokenKind::SignedKeyword)
        flags |= IntegralFlags::Signed;

    result->type = &compilation.getType(operand.type->getBitWidth(), flags);
    return *result;
}

void ConversionExpression::toJson(json& j) const {
    j["operand"] = operand();
}

Expression& DataTypeExpression::fromSyntax(Compilation& compilation, const DataTypeSyntax& syntax,
                                           const BindContext& context) {
    if ((context.flags & BindFlags::AllowDataType) == 0) {
        context.addDiag(diag::ExpectedExpression, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    const Type& type = compilation.getType(syntax, context.lookupLocation, context.scope);
    return *compilation.emplace<DataTypeExpression>(type, syntax.sourceRange());
}

void AssignmentPatternExpressionBase::toJson(json& j) const {
    for (auto elem : elements())
        j["elements"].push_back(*elem);
}

Expression& SimpleAssignmentPatternExpression::forStruct(
    Compilation& comp, const SimpleAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Scope& structScope, SourceRange sourceRange) {

    SmallVectorSized<const Type*, 8> types;
    for (auto& field : structScope.membersOfType<FieldSymbol>())
        types.append(&field.getType());

    if (types.size() != syntax.items.size()) {
        auto& diag = context.addDiag(diag::WrongNumberAssignmentPatterns, sourceRange);
        diag << type << types.size() << syntax.items.size();
        return badExpr(comp, nullptr);
    }

    bool bad = false;
    uint32_t index = 0;
    SmallVectorSized<const Expression*, 8> elems;
    for (auto item : syntax.items) {
        auto& expr =
            Expression::bind(*types[index++], *item, item->getFirstToken().location(), context);
        elems.append(&expr);
        bad |= expr.bad();
    }

    auto result =
        comp.emplace<SimpleAssignmentPatternExpression>(type, elems.copy(comp), sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& SimpleAssignmentPatternExpression::forArray(
    Compilation& comp, const SimpleAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Type& elementType, bitwidth_t numElements, SourceRange sourceRange) {

    bool bad = false;
    SmallVectorSized<const Expression*, 8> elems;
    for (auto item : syntax.items) {
        auto& expr =
            Expression::bind(elementType, *item, item->getFirstToken().location(), context);
        elems.append(&expr);
        bad |= expr.bad();
    }

    if (numElements != syntax.items.size()) {
        auto& diag = context.addDiag(diag::WrongNumberAssignmentPatterns, sourceRange);
        diag << type << numElements << elems.size();
        bad = true;
    }

    auto result =
        comp.emplace<SimpleAssignmentPatternExpression>(type, elems.copy(comp), sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

static bool matchMembers(const BindContext& context, const Scope& structScope,
                         SourceRange sourceRange,
                         SmallMap<const Symbol*, const Expression*, 8>& memberMap,
                         span<const StructuredAssignmentPatternExpression::TypeSetter> typeSetters,
                         const Expression* defaultSetter, SmallVector<const Expression*>& results) {

    const ExpressionSyntax* defaultSyntax = nullptr;
    if (defaultSetter) {
        defaultSyntax = defaultSetter->syntax;
        ASSERT(defaultSyntax);
    }

    // Every member of the structure must be covered by one of:
    // member:value     -- recorded in the memberMap
    // type:value       -- recorded in typeSetters, last one takes precedence
    // default:value    -- recorded in defaultSetter, types must be assignable
    // struct member    -- recursively descend into the struct
    // array member     -- recursively descend into the array
    bool bad = false;
    for (auto& field : structScope.membersOfType<FieldSymbol>()) {
        // If we already have a setter for this field we don't have to do anything else.
        if (auto it = memberMap.find(&field); it != memberMap.end()) {
            results.append(it->second);
            continue;
        }

        const Type& type = field.getType();
        if (type.isError() || field.name.empty()) {
            bad = true;
            continue;
        }

        // Otherwise try all type setters for a match. Last one that matches wins.
        const Expression* found = nullptr;
        for (auto& setter : typeSetters) {
            if (setter.type && type.isMatching(*setter.type))
                found = setter.expr;
        }

        if (found) {
            results.append(found);
            continue;
        }

        // Otherwise, see if we have a default value that can be applied.
        // The default applies if:
        // - The field type matches exactly
        // - The field type is a simple bit vector and the type is assignment compatible
        if (defaultSetter) {
            if (type.isMatching(*defaultSetter->type)) {
                results.append(defaultSetter);
                continue;
            }

            if (type.isSimpleBitVector() && type.isAssignmentCompatible(*defaultSetter->type)) {
                results.append(&Expression::bind(
                    type, *defaultSyntax, defaultSyntax->getFirstToken().location(), context));
                continue;
            }
        }

        // Otherwise, we check first if the type is a struct or array, in which
        // case we descend recursively into its members before continuing on with the default.
        if (type.isStruct()) {
            // TODO:
            continue;
        }
        if (type.isArray()) {
            // TODO:
            continue;
        }

        // Finally, if we have a default then it must now be assignment compatible.
        if (defaultSetter) {
            results.append(&Expression::bind(type, *defaultSyntax,
                                             defaultSyntax->getFirstToken().location(), context));
            continue;
        }

        // Otherwise there's no setter for this member, which is an error.
        context.addDiag(diag::AssignmentPatternNoMember, sourceRange) << field.name;
        bad = true;
    }

    return bad;
}

static bool matchElements(const BindContext& context, const Type& elementType,
                          ConstantRange arrayRange, SourceRange sourceRange,
                          SmallMap<int32_t, const Expression*, 8>& indexMap,
                          span<const StructuredAssignmentPatternExpression::TypeSetter> typeSetters,
                          const Expression* defaultSetter,
                          SmallVector<const Expression*>& results) {
    if (elementType.isError())
        return true;

    const ExpressionSyntax* defaultSyntax = nullptr;
    if (defaultSetter) {
        defaultSyntax = defaultSetter->syntax;
        ASSERT(defaultSyntax);
    }

    // Every element in the array must be covered by one of:
    // index:value      -- recorded in the indexMap
    // type:value       -- recorded in typeSetters, last one takes precedence
    // default:value    -- recorded in defaultSetter, types must be assignable
    // struct element   -- recursively descend into the struct
    // array element    -- recursively descend into the array

    auto determineVal = [&]() -> const Expression* {
        // Otherwise try all type setters for a match. Last one that matches wins.
        const Expression* found = nullptr;
        for (auto& setter : typeSetters) {
            if (setter.type && elementType.isMatching(*setter.type))
                found = setter.expr;
        }

        if (found)
            return found;

        // Otherwise, see if we have a default value that can be applied.
        // The default applies if:
        // - The element type matches exactly
        // - The element type is a simple bit vector and the type is assignment compatible
        if (defaultSetter) {
            if (elementType.isMatching(*defaultSetter->type))
                return defaultSetter;

            if (elementType.isSimpleBitVector() &&
                elementType.isAssignmentCompatible(*defaultSetter->type)) {
                return &Expression::bind(elementType, *defaultSyntax,
                                         defaultSyntax->getFirstToken().location(), context);
            }
        }

        // Otherwise, we check first if the type is a struct or array, in which
        // case we descend recursively into its members before continuing on with the default.
        if (elementType.isStruct()) {
            // TODO:
            return nullptr;
        }
        if (elementType.isArray()) {
            // TODO:
            return nullptr;
        }

        // Finally, if we have a default then it must now be assignment compatible.
        if (defaultSetter) {
            return &Expression::bind(elementType, *defaultSyntax,
                                     defaultSyntax->getFirstToken().location(), context);
        }

        // Otherwise there's no setter for this element, which is an error.
        context.addDiag(diag::AssignmentPatternMissingElements, sourceRange);
        return nullptr;
    };

    optional<const Expression*> cachedVal;
    for (int32_t i = arrayRange.lower(); i <= arrayRange.upper(); i++) {
        // If we already have a setter for this index we don't have to do anything else.
        if (auto it = indexMap.find(i); it != indexMap.end()) {
            results.append(it->second);
            continue;
        }

        if (!cachedVal) {
            cachedVal = determineVal();
            if (!cachedVal.value())
                return true;
        }

        results.append(*cachedVal);
    }

    return false;
}

Expression& StructuredAssignmentPatternExpression::forStruct(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Scope& structScope, SourceRange sourceRange) {

    bool bad = false;
    const Expression* defaultSetter = nullptr;
    SmallMap<const Symbol*, const Expression*, 8> memberMap;
    SmallVectorSized<MemberSetter, 4> memberSetters;
    SmallVectorSized<TypeSetter, 4> typeSetters;

    for (auto item : syntax.items) {
        if (item->key->kind == SyntaxKind::DefaultPatternKeyExpression) {
            if (defaultSetter) {
                context.addDiag(diag::AssignmentPatternKeyDupDefault, item->key->sourceRange());
                bad = true;
            }
            defaultSetter = &selfDetermined(comp, *item->expr, context);
            bad |= defaultSetter->bad();
        }
        else if (item->key->kind == SyntaxKind::IdentifierName) {
            auto nameToken = item->key->as<IdentifierNameSyntax>().identifier;
            auto name = nameToken.valueText();
            if (name.empty()) {
                bad = true;
                continue;
            }

            const Symbol* member = structScope.find(name);
            if (member) {
                auto& expr = bind(member->as<FieldSymbol>().getType(), *item->expr,
                                  nameToken.location(), context);
                bad |= expr.bad();

                memberMap.emplace(member, &expr);
                memberSetters.emplace(MemberSetter{ member, &expr });
            }
            else {
                auto found = context.scope.lookupUnqualifiedName(
                    name, context.lookupLocation, item->key->sourceRange(), LookupFlags::Type);

                if (found && found->isType()) {
                    auto& expr =
                        bind(found->as<Type>(), *item->expr, nameToken.location(), context);
                    bad |= expr.bad();

                    typeSetters.emplace(TypeSetter{ &found->as<Type>(), &expr });
                }
                else {
                    auto& diag = context.addDiag(diag::UnknownMember, item->key->sourceRange());
                    diag << name;
                    diag << type;
                    bad = true;
                }
            }
        }
        else if (DataTypeSyntax::isKind(item->key->kind)) {
            const Type& typeKey = comp.getType(item->key->as<DataTypeSyntax>(),
                                               context.lookupLocation, context.scope);
            auto& expr =
                bind(typeKey, *item->expr, item->expr->getFirstToken().location(), context);

            typeSetters.emplace(TypeSetter{ &typeKey, &expr });
            bad |= expr.bad();
        }
        else {
            context.addDiag(diag::StructAssignmentPatternKey, item->key->sourceRange());
            bad = true;
        }
    }

    SmallVectorSized<const Expression*, 8> elements;
    bad |= matchMembers(context, structScope, syntax.sourceRange(), memberMap, typeSetters,
                        defaultSetter, elements);

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, memberSetters.copy(comp), typeSetters.copy(comp), span<const IndexSetter>{},
        defaultSetter, elements.copy(comp), sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& StructuredAssignmentPatternExpression::forArray(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    bool bad = false;
    const Expression* defaultSetter = nullptr;
    SmallMap<int32_t, const Expression*, 8> indexMap;
    SmallVectorSized<IndexSetter, 4> indexSetters;
    SmallVectorSized<TypeSetter, 4> typeSetters;

    for (auto item : syntax.items) {
        if (item->key->kind == SyntaxKind::DefaultPatternKeyExpression) {
            if (defaultSetter) {
                context.addDiag(diag::AssignmentPatternKeyDupDefault, item->key->sourceRange());
                bad = true;
            }
            defaultSetter = &selfDetermined(comp, *item->expr, context);
            bad |= defaultSetter->bad();
        }
        else if (DataTypeSyntax::isKind(item->key->kind)) {
            const Type& typeKey = comp.getType(item->key->as<DataTypeSyntax>(),
                                               context.lookupLocation, context.scope);
            auto& expr =
                bind(typeKey, *item->expr, item->expr->getFirstToken().location(), context);

            typeSetters.emplace(TypeSetter{ &typeKey, &expr });
            bad |= expr.bad();
        }
        else {
            // TODO: check for type name here

            auto& indexExpr = Expression::bind(*item->key, context, BindFlags::Constant);
            optional<int32_t> index = context.evalInteger(indexExpr);
            if (!index) {
                bad = true;
                continue;
            }

            if (!type.getArrayRange().containsPoint(*index)) {
                auto& diag = context.addDiag(diag::IndexValueInvalid, indexExpr.sourceRange);
                diag << *index;
                diag << type;
                bad = true;
                continue;
            }

            auto& expr =
                bind(elementType, *item->expr, item->expr->getFirstToken().location(), context);
            bad |= expr.bad();

            indexMap.emplace(*index, &expr);
            indexSetters.append(IndexSetter{ &indexExpr, &expr });
        }
    }

    SmallVectorSized<const Expression*, 8> elements;
    bad |= matchElements(context, elementType, type.getArrayRange(), syntax.sourceRange(), indexMap,
                         typeSetters, defaultSetter, elements);

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, span<const MemberSetter>{}, typeSetters.copy(comp), indexSetters.copy(comp),
        defaultSetter, elements.copy(comp), sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

void StructuredAssignmentPatternExpression::toJson(json&) const {
    // TODO:
}

const Expression& ReplicatedAssignmentPatternExpression::bindReplCount(
    Compilation& comp, const ExpressionSyntax& syntax, const BindContext& context, size_t& count) {

    const Expression& expr = bind(syntax, context, BindFlags::Constant);
    optional<int32_t> c = context.evalInteger(expr);
    if (!context.requireGtZero(c, expr.sourceRange))
        return badExpr(comp, &expr);

    count = size_t(*c);
    return expr;
}

Expression& ReplicatedAssignmentPatternExpression::forStruct(
    Compilation& comp, const ReplicatedAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Scope& structScope, SourceRange sourceRange) {

    size_t count;
    auto& countExpr = bindReplCount(comp, *syntax.countExpr, context, count);
    if (countExpr.bad())
        return badExpr(comp, nullptr);

    SmallVectorSized<const Type*, 8> types;
    for (auto& field : structScope.membersOfType<FieldSymbol>())
        types.append(&field.getType());

    if (types.size() != syntax.items.size() * count) {
        auto& diag = context.addDiag(diag::WrongNumberAssignmentPatterns, sourceRange);
        diag << type << types.size() << syntax.items.size() * count;
        return badExpr(comp, nullptr);
    }

    bool bad = false;
    size_t index = 0;
    SmallVectorSized<const Expression*, 8> elems;
    for (size_t i = 0; i < count; i++) {
        for (auto item : syntax.items) {
            auto& expr =
                Expression::bind(*types[index++], *item, item->getFirstToken().location(), context);
            elems.append(&expr);
            bad |= expr.bad();
        }
    }

    auto result = comp.emplace<ReplicatedAssignmentPatternExpression>(
        type, countExpr, elems.copy(comp), sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& ReplicatedAssignmentPatternExpression::forArray(
    Compilation& comp, const ReplicatedAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Type& elementType, bitwidth_t numElements, SourceRange sourceRange) {

    size_t count;
    auto& countExpr = bindReplCount(comp, *syntax.countExpr, context, count);
    if (countExpr.bad())
        return badExpr(comp, nullptr);

    bool bad = false;
    SmallVectorSized<const Expression*, 8> elems;
    for (size_t i = 0; i < count; i++) {
        for (auto item : syntax.items) {
            auto& expr =
                Expression::bind(elementType, *item, item->getFirstToken().location(), context);
            elems.append(&expr);
            bad |= expr.bad();
        }
    }

    if (numElements != elems.size()) {
        auto& diag = context.addDiag(diag::WrongNumberAssignmentPatterns, sourceRange);
        diag << type << numElements << elems.size();
        bad = true;
    }

    auto result = comp.emplace<ReplicatedAssignmentPatternExpression>(
        type, countExpr, elems.copy(comp), sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

void ReplicatedAssignmentPatternExpression::toJson(json& j) const {
    j["count"] = count();
    AssignmentPatternExpressionBase::toJson(j);
}

UnaryOperator getUnaryOperator(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::UnaryPlusExpression:
            return UnaryOperator::Plus;
        case SyntaxKind::UnaryMinusExpression:
            return UnaryOperator::Minus;
        case SyntaxKind::UnaryBitwiseNotExpression:
            return UnaryOperator::BitwiseNot;
        case SyntaxKind::UnaryBitwiseAndExpression:
            return UnaryOperator::BitwiseAnd;
        case SyntaxKind::UnaryBitwiseOrExpression:
            return UnaryOperator::BitwiseOr;
        case SyntaxKind::UnaryBitwiseXorExpression:
            return UnaryOperator::BitwiseXor;
        case SyntaxKind::UnaryBitwiseNandExpression:
            return UnaryOperator::BitwiseNand;
        case SyntaxKind::UnaryBitwiseNorExpression:
            return UnaryOperator::BitwiseNor;
        case SyntaxKind::UnaryBitwiseXnorExpression:
            return UnaryOperator::BitwiseXnor;
        case SyntaxKind::UnaryLogicalNotExpression:
            return UnaryOperator::LogicalNot;
        case SyntaxKind::UnaryPreincrementExpression:
            return UnaryOperator::Preincrement;
        case SyntaxKind::UnaryPredecrementExpression:
            return UnaryOperator::Predecrement;
        case SyntaxKind::PostincrementExpression:
            return UnaryOperator::Postincrement;
        case SyntaxKind::PostdecrementExpression:
            return UnaryOperator::Postdecrement;
        default:
            THROW_UNREACHABLE;
    }
}

BinaryOperator getBinaryOperator(SyntaxKind kind) {
    switch (kind) {
        case SyntaxKind::AddExpression:
            return BinaryOperator::Add;
        case SyntaxKind::SubtractExpression:
            return BinaryOperator::Subtract;
        case SyntaxKind::MultiplyExpression:
            return BinaryOperator::Multiply;
        case SyntaxKind::DivideExpression:
            return BinaryOperator::Divide;
        case SyntaxKind::ModExpression:
            return BinaryOperator::Mod;
        case SyntaxKind::BinaryAndExpression:
            return BinaryOperator::BinaryAnd;
        case SyntaxKind::BinaryOrExpression:
            return BinaryOperator::BinaryOr;
        case SyntaxKind::BinaryXorExpression:
            return BinaryOperator::BinaryXor;
        case SyntaxKind::BinaryXnorExpression:
            return BinaryOperator::BinaryXnor;
        case SyntaxKind::EqualityExpression:
            return BinaryOperator::Equality;
        case SyntaxKind::InequalityExpression:
            return BinaryOperator::Inequality;
        case SyntaxKind::CaseEqualityExpression:
            return BinaryOperator::CaseEquality;
        case SyntaxKind::CaseInequalityExpression:
            return BinaryOperator::CaseInequality;
        case SyntaxKind::GreaterThanEqualExpression:
            return BinaryOperator::GreaterThanEqual;
        case SyntaxKind::GreaterThanExpression:
            return BinaryOperator::GreaterThan;
        case SyntaxKind::LessThanEqualExpression:
            return BinaryOperator::LessThanEqual;
        case SyntaxKind::LessThanExpression:
            return BinaryOperator::LessThan;
        case SyntaxKind::WildcardEqualityExpression:
            return BinaryOperator::WildcardEquality;
        case SyntaxKind::WildcardInequalityExpression:
            return BinaryOperator::WildcardInequality;
        case SyntaxKind::LogicalAndExpression:
            return BinaryOperator::LogicalAnd;
        case SyntaxKind::LogicalOrExpression:
            return BinaryOperator::LogicalOr;
        case SyntaxKind::LogicalImplicationExpression:
            return BinaryOperator::LogicalImplication;
        case SyntaxKind::LogicalEquivalenceExpression:
            return BinaryOperator::LogicalEquivalence;
        case SyntaxKind::LogicalShiftLeftExpression:
            return BinaryOperator::LogicalShiftLeft;
        case SyntaxKind::LogicalShiftRightExpression:
            return BinaryOperator::LogicalShiftRight;
        case SyntaxKind::ArithmeticShiftLeftExpression:
            return BinaryOperator::ArithmeticShiftLeft;
        case SyntaxKind::ArithmeticShiftRightExpression:
            return BinaryOperator::ArithmeticShiftRight;
        case SyntaxKind::PowerExpression:
            return BinaryOperator::Power;
        case SyntaxKind::AddAssignmentExpression:
            return BinaryOperator::Add;
        case SyntaxKind::SubtractAssignmentExpression:
            return BinaryOperator::Subtract;
        case SyntaxKind::MultiplyAssignmentExpression:
            return BinaryOperator::Multiply;
        case SyntaxKind::DivideAssignmentExpression:
            return BinaryOperator::Divide;
        case SyntaxKind::ModAssignmentExpression:
            return BinaryOperator::Mod;
        case SyntaxKind::AndAssignmentExpression:
            return BinaryOperator::BinaryAnd;
        case SyntaxKind::OrAssignmentExpression:
            return BinaryOperator::BinaryOr;
        case SyntaxKind::XorAssignmentExpression:
            return BinaryOperator::BinaryXor;
        case SyntaxKind::LogicalLeftShiftAssignmentExpression:
            return BinaryOperator::LogicalShiftLeft;
        case SyntaxKind::LogicalRightShiftAssignmentExpression:
            return BinaryOperator::LogicalShiftRight;
        case SyntaxKind::ArithmeticLeftShiftAssignmentExpression:
            return BinaryOperator::ArithmeticShiftLeft;
        case SyntaxKind::ArithmeticRightShiftAssignmentExpression:
            return BinaryOperator::ArithmeticShiftRight;
        default:
            THROW_UNREACHABLE;
    }
}

} // namespace slang
