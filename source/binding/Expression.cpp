//------------------------------------------------------------------------------
// Expression.cpp
// Expression creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/Expression.h"

#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/ASTVisitor.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"
#include "slang/types/Type.h"

namespace {

using namespace slang;

struct EvalVisitor {
    template<typename T>
    ConstantValue visit(const T& expr, EvalContext& context) {
        if (expr.bad())
            return nullptr;

        if (expr.constant)
            return *expr.constant;

        ConstantValue cv = expr.evalImpl(context);
        if (cv && context.cacheResults()) {
            expr.constant = context.compilation.allocConstant(std::move(cv));
            return *expr.constant;
        }

        return cv;
    }

    ConstantValue visitInvalid(const Expression&, EvalContext&) { return nullptr; }
};

class LValueVisitor {
    template<typename T, typename Arg>
    using evalLValue_t = decltype(std::declval<T>().evalLValueImpl(std::declval<Arg>()));

public:
    template<typename T>
    LValue visit(const T& expr, EvalContext& context) {
        if constexpr (is_detected_v<evalLValue_t, T, EvalContext&>) {
            if (expr.bad())
                return nullptr;

            return expr.evalLValueImpl(context);
        }
        else {
            (void)expr;
            (void)context;
            THROW_UNREACHABLE;
        }
    }

    LValue visitInvalid(const Expression&, EvalContext&) { return nullptr; }
};

struct VerifyVisitor {
    template<typename T>
    bool visit(const T& expr, EvalContext& context) {
        if (expr.bad())
            return false;

        return expr.verifyConstantImpl(context);
    }

    bool visitInvalid(const Expression&, EvalContext&) { return false; }
};

class EffectiveWidthVisitor {
    template<typename T>
    using getEffectiveWidth_t = decltype(std::declval<T>().getEffectiveWidthImpl());

public:
    template<typename T>
    optional<bitwidth_t> visit(const T& expr) {
        if constexpr (is_detected_v<getEffectiveWidth_t, T>) {
            if (expr.bad())
                return std::nullopt;

            return expr.getEffectiveWidthImpl();
        }
        else {
            return expr.type->getBitWidth();
        }
    }

    optional<bitwidth_t> visitInvalid(const Expression&) { return std::nullopt; }
};

} // namespace

namespace slang {

// This visitor handles inserting implicit conversions into an expression
// tree where necessary. SystemVerilog has an additional weird feature where
// the type of one branch of an expression tree can bubble up and then propagate
// back down a different branch, which is also implemented here.
struct Expression::PropagationVisitor {
    template<typename T, typename... Args>
    using propagate_t = decltype(std::declval<T>().propagateType(std::declval<Args>()...));

    const BindContext& context;
    const Type& newType;
    SourceLocation assignmentLoc;

    PropagationVisitor(const BindContext& context, const Type& newType,
                       SourceLocation assignmentLoc) :
        context(context),
        newType(newType), assignmentLoc(assignmentLoc) {}

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
        if constexpr (is_detected_v<propagate_t, T, const BindContext&, const Type&>) {
            if ((newType.isFloating() && expr.type->isFloating()) ||
                (newType.isIntegral() && expr.type->isIntegral()) || newType.isString() ||
                expr.kind == ExpressionKind::OpenRange) {

                if (expr.propagateType(context, newType))
                    needConversion = false;
            }
        }

        Expression* result = &expr;
        if (needConversion) {
            if (assignmentLoc) {
                result = &ConversionExpression::makeImplicit(
                    context, newType, ConversionKind::Implicit, expr, assignmentLoc);
            }
            else {
                result = &ConversionExpression::makeImplicit(
                    context, newType, ConversionKind::Propagated, expr, expr.sourceRange.start());
            }
        }

        return *result;
    }

    Expression& visitInvalid(Expression& expr) { return expr; }
};

const InvalidExpression InvalidExpression::Instance(nullptr, ErrorType::Instance);

const Expression& Expression::bind(const ExpressionSyntax& syntax, const BindContext& context,
                                   bitmask<BindFlags> extraFlags) {
    const Expression& result =
        selfDetermined(context.scope.getCompilation(), syntax, context, extraFlags);
    return checkBindFlags(result, context.resetFlags(extraFlags));
}

const Expression& Expression::bindLValue(const ExpressionSyntax& lhs, const Type& rhs,
                                         SourceLocation location, const BindContext& context,
                                         bool isInout) {
    Compilation& comp = context.scope.getCompilation();

    // Create a placeholder expression that will carry the type of the rhs.
    // Nothing will ever actually look at this expression, it's there only
    // to fill the space in the created AssignmentExpression.
    SourceRange rhsRange{ location, location };
    auto rhsExpr = comp.emplace<EmptyArgumentExpression>(rhs, rhsRange);
    if (rhsExpr->bad())
        return badExpr(comp, nullptr);

    Expression* lhsExpr = (lhs.kind == SyntaxKind::StreamingConcatenationExpression && !isInout &&
                           !(context.instance && !context.instance->arrayPath.empty()))
                              ? &selfDetermined(comp, lhs, context, BindFlags::StreamingAllowed)
                              : &create(comp, lhs, context, BindFlags::None, rhsExpr->type);
    selfDetermined(context, lhsExpr);

    SourceRange lhsRange = lhs.sourceRange();
    auto& result = AssignmentExpression::fromComponents(
        comp, std::nullopt, /* nonBlocking */ false, *lhsExpr, *rhsExpr, lhsRange.start(),
        /* timingControl */ nullptr, lhsRange, context);

    return checkBindFlags(result, context);
}

const Expression& Expression::bindRValue(const Type& lhs, const ExpressionSyntax& rhs,
                                         SourceLocation location, const BindContext& context) {
    Compilation& comp = context.scope.getCompilation();

    bitmask<BindFlags> extraFlags = context.instance && !context.instance->arrayPath.empty()
                                        ? BindFlags::None
                                        : BindFlags::StreamingAllowed;
    Expression& expr = create(comp, rhs, context, extraFlags, &lhs);

    const Expression& result = convertAssignment(context, lhs, expr, location);
    return checkBindFlags(result, context);
}

const Expression& Expression::bindRefArg(const Type& lhs, bool isConstRef,
                                         const ExpressionSyntax& rhs, SourceLocation location,
                                         const BindContext& context) {
    Compilation& comp = context.scope.getCompilation();
    Expression& expr = selfDetermined(comp, rhs, context);
    if (expr.bad())
        return expr;

    if (lhs.isError())
        return badExpr(comp, &expr);

    if (!expr.canConnectToRefArg(isConstRef)) {
        // If we can't bind to ref but we can bind to 'const ref', issue a more
        // specific error about constness.
        DiagCode code = diag::InvalidRefArg;
        if (!isConstRef && expr.canConnectToRefArg(true))
            code = diag::ConstVarToRef;

        context.addDiag(code, location) << expr.sourceRange;
        return badExpr(comp, &expr);
    }

    if (!lhs.isEquivalent(*expr.type)) {
        auto& diag = context.addDiag(diag::RefTypeMismatch, location) << expr.sourceRange;
        diag << *expr.type << lhs;
        return badExpr(comp, &expr);
    }

    return checkBindFlags(expr, context);
}

const Expression& Expression::bindArgument(const Type& argType, ArgumentDirection direction,
                                           const ExpressionSyntax& syntax,
                                           const BindContext& context, bool isConstRef) {
    auto loc = syntax.getFirstToken().location();
    switch (direction) {
        case ArgumentDirection::In:
            return bindRValue(argType, syntax, loc, context);
        case ArgumentDirection::Out:
        case ArgumentDirection::InOut:
            // TODO: additional restrictions on inout
            return bindLValue(syntax, argType, loc, context, direction == ArgumentDirection::InOut);
        case ArgumentDirection::Ref:
            return bindRefArg(argType, isConstRef, syntax, loc, context);
    }
    THROW_UNREACHABLE;
}

const Expression& Expression::bindImplicitParam(const DataTypeSyntax& typeSyntax,
                                                const ExpressionSyntax& rhs,
                                                SourceLocation location,
                                                const BindContext& context) {
    Compilation& comp = context.scope.getCompilation();
    Expression& expr = create(comp, rhs, context);
    const Type* lhsType = expr.type;

    // Rules are described in [6.20.2].
    auto& it = typeSyntax.as<ImplicitTypeSyntax>();
    if (!it.dimensions.empty()) {
        // If we have a range provided, the result is always an integral value
        // of the provided width -- getType() will do what we want here.
        lhsType = &comp.getType(typeSyntax, context.lookupLocation, context.scope);
    }
    else if (it.signing) {
        // If signing is provided, the result is always integral but we infer the width.
        // If the type is non-integral or unsized, infer a width of 32.
        bitwidth_t bits = lhsType->getBitWidth();
        if (!lhsType->isIntegral() || expr.isUnsizedInteger())
            bits = 32;

        bitmask<IntegralFlags> flags = IntegralFlags::FourState;
        if (it.signing.kind == TokenKind::SignedKeyword)
            flags |= IntegralFlags::Signed;

        lhsType = &comp.getType(bits, flags);
    }
    else {
        // Neither range nor signing provided, so infer from the expression type.
        // If integral, infer using rules mentioned above. Otherwise just take the type.
        if (lhsType->isIntegral()) {
            bitwidth_t bits = lhsType->getBitWidth();
            if (expr.isUnsizedInteger())
                bits = 32;

            // Keep the signed flag but force four state.
            auto flags = lhsType->getIntegralFlags();
            flags |= IntegralFlags::FourState;

            lhsType = &comp.getType(bits, flags);
        }
    }

    const Expression& result = convertAssignment(context, *lhsType, expr, location);
    return checkBindFlags(result, context);
}

const Expression& Expression::checkBindFlags(const Expression& expr, const BindContext& context) {
    if ((context.flags & BindFlags::Constant) == 0)
        return expr;

    EvalContext verifyContext(context.getCompilation(), EvalFlags::IsVerifying);
    bool ok = expr.verifyConstant(verifyContext);
    verifyContext.reportDiags(context);

    if (!ok)
        return badExpr(context.getCompilation(), &expr);
    return expr;
}

ConstantValue Expression::eval(EvalContext& context) const {
    EvalVisitor visitor;
    return visit(visitor, context);
}

LValue Expression::evalLValue(EvalContext& context) const {
    LValueVisitor visitor;
    return visit(visitor, context);
}

bool Expression::verifyConstant(EvalContext& context) const {
    VerifyVisitor visitor;
    return visit(visitor, context);
}

bool Expression::verifyAssignable(const BindContext& context, bool isNonBlocking,
                                  SourceLocation location) const {
    switch (kind) {
        case ExpressionKind::NamedValue: {
            auto& nv = as<NamedValueExpression>();
            return nv.verifyAssignableImpl(context, isNonBlocking, location);
        }
        case ExpressionKind::HierarchicalValue: {
            auto& hv = as<HierarchicalValueExpression>();
            return hv.verifyAssignableImpl(context, isNonBlocking, location);
        }
        case ExpressionKind::ElementSelect: {
            auto& select = as<ElementSelectExpression>();
            return select.value().verifyAssignable(context, isNonBlocking, location);
        }
        case ExpressionKind::RangeSelect: {
            auto& select = as<RangeSelectExpression>();
            return select.value().verifyAssignable(context, isNonBlocking, location);
        }
        case ExpressionKind::MemberAccess: {
            auto& access = as<MemberAccessExpression>();
            return access.verifyAssignableImpl(context, isNonBlocking, location);
        }
        case ExpressionKind::Concatenation: {
            auto& concat = as<ConcatenationExpression>();
            if (!concat.type->isIntegral())
                break;

            for (auto op : concat.operands()) {
                if (!op->verifyAssignable(context, isNonBlocking, location))
                    return false;
            }
            return true;
        }
        case ExpressionKind::Streaming: {
            auto& stream = as<StreamingConcatenationExpression>();
            for (auto op : stream.streams()) {
                if (!op->operand->verifyAssignable(context, isNonBlocking, location))
                    return false;
            }
            return true;
        }
        default:
            break;
    }

    if (!location)
        location = sourceRange.start();

    auto& diag = context.addDiag(diag::ExpressionNotAssignable, location);
    diag << sourceRange;
    return false;
}

bool Expression::canConnectToRefArg(bool isConstRef, bool allowConstClassHandle) const {
    auto canConnectSymbol = [&](const Symbol& sym) {
        if (!VariableSymbol::isKind(sym.kind))
            return false;

        auto& var = sym.as<VariableSymbol>();
        return isConstRef || !var.isConstant || (allowConstClassHandle && var.getType().isClass());
    };

    switch (kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
            return canConnectSymbol(as<ValueExpressionBase>().symbol);
        case ExpressionKind::ElementSelect: {
            auto& val = as<ElementSelectExpression>().value();
            return val.type->isUnpackedArray() && val.canConnectToRefArg(isConstRef, false);
        }
        case ExpressionKind::MemberAccess: {
            auto& access = as<MemberAccessExpression>();
            auto& val = access.value();
            return (val.type->isClass() || val.type->isUnpackedStruct()) &&
                   val.canConnectToRefArg(isConstRef, true) && canConnectSymbol(access.member);
        }
        default:
            return false;
    }
}

optional<bitwidth_t> Expression::getEffectiveWidth() const {
    EffectiveWidthVisitor visitor;
    return visit(visitor);
}

bool Expression::bad() const {
    return kind == ExpressionKind::Invalid || type->isError();
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
        case ExpressionKind::OpenRange: {
            auto& range = as<OpenRangeExpression>();
            return range.left().isImplicitString() || range.right().isImplicitString();
        }
        case ExpressionKind::MinTypMax: {
            auto& mtm = as<MinTypMaxExpression>();
            return mtm.selected().isImplicitString();
        }
        case ExpressionKind::NamedValue: {
            auto& nv = as<NamedValueExpression>();
            return nv.symbol.kind == SymbolKind::Parameter &&
                   nv.symbol.as<ParameterSymbol>().isImplicitString();
        }
        case ExpressionKind::Conversion: {
            auto& conv = as<ConversionExpression>();
            return conv.isImplicit() && conv.operand().isImplicitString();
        }
        default:
            return false;
    }
}

bool Expression::isUnsizedInteger() const {
    switch (kind) {
        case ExpressionKind::UnbasedUnsizedIntegerLiteral:
            return true;
        case ExpressionKind::IntegerLiteral:
            return as<IntegerLiteral>().isDeclaredUnsized;
        case ExpressionKind::MinTypMax:
            return as<MinTypMaxExpression>().selected().isUnsizedInteger();
        default:
            return false;
    }
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
        case SyntaxKind::TimeLiteralExpression:
            result = &TimeLiteral::fromSyntax(context, syntax.as<LiteralExpressionSyntax>());
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
            // Parenthesis re-allows assignments if we're in a procedural statement.
            if (context.flags & BindFlags::ProceduralStatement)
                extraFlags |= BindFlags::AssignmentAllowed;

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
        case SyntaxKind::NonblockingAssignmentExpression:
            result = &AssignmentExpression::fromSyntax(
                compilation, syntax.as<BinaryExpressionSyntax>(), context);
            break;
        case SyntaxKind::InvocationExpression:
            result = &CallExpression::fromSyntax(
                compilation, syntax.as<InvocationExpressionSyntax>(), nullptr, context);
            break;
        case SyntaxKind::ConditionalExpression:
            result = &ConditionalExpression::fromSyntax(
                compilation, syntax.as<ConditionalExpressionSyntax>(), context, assignmentTarget);
            break;
        case SyntaxKind::InsideExpression:
            result = &InsideExpression::fromSyntax(compilation, syntax.as<InsideExpressionSyntax>(),
                                                   context);
            break;
        case SyntaxKind::MemberAccessExpression:
            result = &MemberAccessExpression::fromSyntax(
                compilation, syntax.as<MemberAccessExpressionSyntax>(), nullptr, nullptr, context);
            break;
        case SyntaxKind::ConcatenationExpression:
            result = &ConcatenationExpression::fromSyntax(
                compilation, syntax.as<ConcatenationExpressionSyntax>(), context, assignmentTarget);
            break;
        case SyntaxKind::EmptyQueueExpression:
            result = &ConcatenationExpression::fromEmpty(
                compilation, syntax.as<EmptyQueueExpressionSyntax>(), context, assignmentTarget);
            break;
        case SyntaxKind::MultipleConcatenationExpression:
            result = &ReplicationExpression::fromSyntax(
                compilation, syntax.as<MultipleConcatenationExpressionSyntax>(), context);
            break;
        case SyntaxKind::StreamingConcatenationExpression:
            result = &StreamingConcatenationExpression::fromSyntax(
                compilation, syntax.as<StreamingConcatenationExpressionSyntax>(), context,
                assignmentTarget);
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
        case SyntaxKind::OpenRangeExpression:
            result = &OpenRangeExpression::fromSyntax(
                compilation, syntax.as<OpenRangeExpressionSyntax>(), context);
            break;
        case SyntaxKind::TimingControlExpression:
            // Valid cases of this expression type are handled in AssignmentExpression. If we reach
            // this block here, the expression is invalid so always report an error.
            context.addDiag(diag::TimingControlNotAllowed, syntax.sourceRange());
            result = &badExpr(compilation, nullptr);
            break;
        case SyntaxKind::NewArrayExpression:
            result = &NewArrayExpression::fromSyntax(
                compilation, syntax.as<NewArrayExpressionSyntax>(), context, assignmentTarget);
            break;
        case SyntaxKind::NewClassExpression:
            result = &NewClassExpression::fromSyntax(
                compilation, syntax.as<NewClassExpressionSyntax>(), context, assignmentTarget);
            break;
        case SyntaxKind::CopyClassExpression:
            result = &CopyClassExpression::fromSyntax(
                compilation, syntax.as<CopyClassExpressionSyntax>(), context);
            break;
        case SyntaxKind::DefaultPatternKeyExpression:
            // This should not be reachable from any valid expression binding.
            context.addDiag(diag::ExpectedExpression, syntax.sourceRange());
            result = &badExpr(compilation, nullptr);
            break;
        case SyntaxKind::MinTypMaxExpression:
            result = &MinTypMaxExpression::fromSyntax(
                compilation, syntax.as<MinTypMaxExpressionSyntax>(), context, assignmentTarget);
            break;
        case SyntaxKind::ArrayOrRandomizeMethodExpression:
            result = &CallExpression::fromSyntax(
                compilation, syntax.as<ArrayOrRandomizeMethodExpressionSyntax>(), context);
            break;
        case SyntaxKind::AcceptOnPropertyExpression:
        case SyntaxKind::AlwaysPropertyExpression:
        case SyntaxKind::AndSequenceExpression:
        case SyntaxKind::BinarySequenceDelayExpression:
        case SyntaxKind::EventuallyPropertyExpression:
        case SyntaxKind::ExpressionOrDist:
        case SyntaxKind::IffPropertyExpression:
        case SyntaxKind::ImpliesPropertyExpression:
        case SyntaxKind::IntersectSequenceExpression:
        case SyntaxKind::NextTimePropertyExpression:
        case SyntaxKind::NonOverlappedFollowedByPropertyExpression:
        case SyntaxKind::NonOverlappedImplicationPropertyExpression:
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
        case SyntaxKind::SyncAcceptOnPropertyExpression:
        case SyntaxKind::SyncRejectOnPropertyExpression:
        case SyntaxKind::TaggedUnionExpression:
        case SyntaxKind::ThroughoutSequenceExpression:
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
                result = &bindName(compilation, syntax.as<NameSyntax>(), nullptr, nullptr, context);
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
                                 const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                 const BindContext& context) {
    // If we're in an array iterator expression, the iterator variable needs to be findable
    // even though it's not added to any scope. Check for that case and manually look for
    // its name here.
    if (context.activeIterator) {
        LookupResult result;
        if (Lookup::matchSymbol(context.scope, *context.activeIterator, syntax, result)) {
            return bindLookupResult(compilation, result, syntax.sourceRange(), invocation,
                                    withClause, context);
        }
    }

    bitmask<LookupFlags> flags = LookupFlags::None;
    if (invocation && invocation->arguments)
        flags |= LookupFlags::AllowDeclaredAfter;
    if ((context.flags & BindFlags::Constant) || (context.flags & BindFlags::NoHierarchicalNames))
        flags |= LookupFlags::Constant;

    LookupResult result;
    Lookup::name(context.scope, syntax, context.lookupLocation, flags, result);
    result.reportErrors(context);

    if (result.systemSubroutine) {
        // There won't be any selectors here; this gets checked in the lookup call.
        ASSERT(result.selectors.empty());

        SourceRange callRange = invocation ? invocation->sourceRange() : syntax.sourceRange();
        CallExpression::SystemCallInfo callInfo{ result.systemSubroutine, &context.scope };
        return CallExpression::fromLookup(compilation, callInfo, nullptr, invocation, withClause,
                                          callRange, context);
    }

    const Symbol* symbol = result.found;
    if (!symbol)
        return badExpr(compilation, nullptr);

    if (symbol->isType() && (context.flags & BindFlags::AllowDataType) != 0) {
        // We looked up a named data type and we were allowed to do so, so return it.
        ASSERT(!invocation && !withClause);
        const Type& resultType = Type::fromLookupResult(compilation, result, syntax,
                                                        context.lookupLocation, context.scope);
        return *compilation.emplace<DataTypeExpression>(resultType, syntax.sourceRange());
    }

    // Recursive function call
    if (invocation && symbol->kind == SymbolKind::Variable && result.selectors.empty()) {
        // TODO: check nested scopes?
        auto scope = symbol->getParentScope();
        if (scope && scope->asSymbol().kind == SymbolKind::Subroutine &&
            scope->asSymbol().as<SubroutineSymbol>().returnValVar == symbol) {
            ASSERT(scope->asSymbol().as<SubroutineSymbol>().subroutineKind ==
                   SubroutineKind::Function);
            symbol = &scope->asSymbol();
        }
    }

    result.found = symbol;
    return bindLookupResult(compilation, result, syntax.sourceRange(), invocation, withClause,
                            context);
}

Expression& Expression::bindLookupResult(Compilation& compilation, const LookupResult& result,
                                         SourceRange sourceRange,
                                         const InvocationExpressionSyntax* invocation,
                                         const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                         const BindContext& context) {
    const Symbol* symbol = result.found;
    Expression* expr;
    if (symbol->kind == SymbolKind::Subroutine) {
        SourceRange callRange = invocation ? invocation->sourceRange() : sourceRange;
        expr = &CallExpression::fromLookup(compilation, &symbol->as<SubroutineSymbol>(), nullptr,
                                           invocation, withClause, callRange, context);
        invocation = nullptr;
        withClause = nullptr;
    }
    else {
        expr =
            &ValueExpressionBase::fromSymbol(context, *symbol, result.isHierarchical, sourceRange);
    }

    // Drill down into member accesses.
    for (const auto& selector : result.selectors) {
        if (expr->bad())
            return *expr;

        auto memberSelect = std::get_if<LookupResult::MemberSelector>(&selector);
        if (memberSelect) {
            expr = &MemberAccessExpression::fromSelector(compilation, *expr, *memberSelect,
                                                         invocation, withClause, context);
            if (expr->kind == ExpressionKind::Call) {
                invocation = nullptr;
                withClause = nullptr;
            }
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
                                                   : sourceRange.start();
        auto& diag = context.addDiag(diag::ExpressionNotCallable, loc);
        diag << sourceRange;
        return badExpr(compilation, nullptr);
    }
    else if (withClause && !expr->bad()) {
        context.addDiag(diag::UnexpectedWithClause, withClause->with.range());
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

void Expression::findPotentiallyImplicitNets(const ExpressionSyntax& expr,
                                             const BindContext& context,
                                             SmallVector<Token>& results) {
    struct Visitor : public SyntaxVisitor<Visitor> {
        Visitor(const BindContext& context, SmallVector<Token>& results) :
            context(context), results(results) {}

        void handle(const NameSyntax& nameSyntax) {
            if (nameSyntax.kind != SyntaxKind::IdentifierName)
                return;

            LookupResult result;
            Lookup::name(context.scope, nameSyntax, LookupLocation::max,
                         LookupFlags::NoUndeclaredError, result);

            if (!result.found && !result.hasError())
                results.append(nameSyntax.as<IdentifierNameSyntax>().identifier);
        }

        const BindContext& context;
        SmallVector<Token>& results;
    };

    Visitor visitor(context, results);
    expr.visit(visitor);
}

void Expression::contextDetermined(const BindContext& context, Expression*& expr,
                                   const Type& newType, SourceLocation assignmentLoc) {
    PropagationVisitor visitor(context, newType, assignmentLoc);
    expr = &expr->visit(visitor);
}

void Expression::selfDetermined(const BindContext& context, Expression*& expr) {
    ASSERT(expr->type);
    PropagationVisitor visitor(context, *expr->type, {});
    expr = &expr->visit(visitor);
}

Expression& Expression::selfDetermined(Compilation& compilation, const ExpressionSyntax& syntax,
                                       const BindContext& context, bitmask<BindFlags> extraFlags) {
    Expression* expr = &create(compilation, syntax, context, extraFlags);
    selfDetermined(context, expr);
    return *expr;
}

Expression& Expression::badExpr(Compilation& compilation, const Expression* expr) {
    return *compilation.emplace<InvalidExpression>(expr, compilation.getErrorType());
}

void InvalidExpression::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

} // namespace slang
