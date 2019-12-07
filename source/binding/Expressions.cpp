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
#include "slang/symbols/ASTVisitor.h"
#include "slang/symbols/Type.h"
#include "slang/syntax/AllSyntax.h"

namespace {

using namespace slang;

struct EvalVisitor {
    template<typename T>
    ConstantValue visit(const T& expr, EvalContext& context) {
        // If the expression is already known to be constant just return the value we have.
        if (expr.constant)
            return *expr.constant;

        if (expr.bad())
            return nullptr;

        // Otherwise evaluate and return that.
        return expr.evalImpl(context);
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

} // namespace

namespace slang {

// This visitor handles inserting implicit conversions into an expression tree where necessary.
// SystemVerilog has an additional weird feature where the type of one branch of an expression
// tree can bubble up and then propagate back down a different branch, which is also implemented
// here.
struct Expression::PropagationVisitor {
    template<typename T, typename... Args>
    using propagate_t = decltype(std::declval<T>().propagateType(std::declval<Args>()...));

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
        if constexpr (is_detected_v<propagate_t, T, const BindContext&, const Type&>) {
            if ((newType.isFloating() && expr.type->isFloating()) ||
                (newType.isIntegral() && expr.type->isIntegral()) || newType.isString() ||
                expr.kind == ExpressionKind::OpenRange) {

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

void Expression::checkBindFlags(const Expression& expr, const BindContext& context) {
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
        case ExpressionKind::OpenRange: {
            auto& range = as<OpenRangeExpression>();
            return range.left().isImplicitString() || range.right().isImplicitString();
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
        case SyntaxKind::NonblockingAssignmentExpression:
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
        case SyntaxKind::InsideExpression:
            result = &InsideExpression::fromSyntax(compilation, syntax.as<InsideExpressionSyntax>(),
                                                   context);
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
        case SyntaxKind::OpenRangeExpression:
            result = &OpenRangeExpression::fromSyntax(
                compilation, syntax.as<OpenRangeExpressionSyntax>(), context);
            break;
        case SyntaxKind::AcceptOnPropertyExpression:
        case SyntaxKind::AlwaysPropertyExpression:
        case SyntaxKind::AndSequenceExpression:
        case SyntaxKind::ArrayOrRandomizeMethodExpression:
        case SyntaxKind::BinarySequenceDelayExpression:
        case SyntaxKind::DefaultPatternKeyExpression:
        case SyntaxKind::EmptyQueueExpression:
        case SyntaxKind::EventuallyPropertyExpression:
        case SyntaxKind::ExpressionOrDist:
        case SyntaxKind::IffPropertyExpression:
        case SyntaxKind::ImpliesPropertyExpression:
        case SyntaxKind::IntersectSequenceExpression:
        case SyntaxKind::MinTypMaxExpression:
        case SyntaxKind::NewArrayExpression:
        case SyntaxKind::NewClassExpression:
        case SyntaxKind::NewExpression:
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

Expression& Expression::badExpr(Compilation& compilation, const Expression* expr) {
    return *compilation.emplace<InvalidExpression>(expr, compilation.getErrorType());
}

void InvalidExpression::toJson(json& j) const {
    if (child)
        j["child"] = *child;
}

} // namespace slang
