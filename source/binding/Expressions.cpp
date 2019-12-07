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
#include "slang/util/StackContainer.h"

namespace {

using namespace slang;

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

Expression& Expression::bindAssignmentPattern(Compilation& comp,
                                              const AssignmentPatternExpressionSyntax& syntax,
                                              const BindContext& context,
                                              const Type* assignmentTarget) {
    SourceRange range = syntax.sourceRange();

    if (syntax.type) {
        // TODO: allow type references here
        assignmentTarget = &comp.getType(*syntax.type, context.lookupLocation, context.scope);
        if (assignmentTarget->kind != SymbolKind::TypeAlias &&
            assignmentTarget->kind != SymbolKind::PredefinedIntegerType) {
            context.addDiag(diag::BadAssignmentPatternType, range) << *assignmentTarget;
            return badExpr(comp, nullptr);
        }
    }

    if (!assignmentTarget || assignmentTarget->isError()) {
        if (!assignmentTarget)
            context.addDiag(diag::AssignmentPatternNoContext, syntax.sourceRange());
        return badExpr(comp, nullptr);
    }

    const Type& type = *assignmentTarget;
    const Scope* structScope = nullptr;
    const Type* elementType = nullptr;
    bitwidth_t numElements = 0;

    auto& ct = type.getCanonicalType();
    if (ct.kind == SymbolKind::PackedStructType)
        structScope = &ct.as<PackedStructType>();
    else if (ct.kind == SymbolKind::UnpackedStructType)
        structScope = &ct.as<UnpackedStructType>();
    else if (ct.kind == SymbolKind::PackedArrayType) {
        auto& ua = ct.as<PackedArrayType>();
        elementType = &ua.elementType;
        numElements = ua.range.width();
    }
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

Expression& Expression::badExpr(Compilation& compilation, const Expression* expr) {
    return *compilation.emplace<InvalidExpression>(expr, compilation.getErrorType());
}

void InvalidExpression::toJson(json& j) const {
    if (child)
        j["child"] = *child;
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
            switch (actualArgs[i]->kind) {
                case SyntaxKind::OrderedArgument: {
                    const auto& arg = actualArgs[i]->as<OrderedArgumentSyntax>();
                    buffer.append(&subroutine.bindArgument(i, context, *arg.expr));
                    break;
                }
                case SyntaxKind::NamedArgument:
                    context.addDiag(diag::NamedArgNotAllowed, actualArgs[i]->sourceRange());
                    return badExpr(compilation, nullptr);
                case SyntaxKind::EmptyArgument:
                    if (subroutine.allowEmptyArgument(i)) {
                        buffer.append(compilation.emplace<EmptyArgumentExpression>(
                            compilation.getVoidType(), actualArgs[i]->sourceRange()));
                    }
                    else {
                        context.addDiag(diag::EmptyArgNotAllowed, actualArgs[i]->sourceRange());
                        return badExpr(compilation, nullptr);
                    }
                    break;
                default:
                    THROW_UNREACHABLE;
            }
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

string_view CallExpression::getSubroutineName() const {
    if (subroutine.index() == 1) {
        const SystemSubroutine& systemSubroutine = *std::get<1>(subroutine);
        return systemSubroutine.name;
    }

    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    return symbol.name;
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
        if (!result->type->isSimpleType() && !result->type->isError() &&
            !result->type->isString()) {
            context.addDiag(diag::BadCastType, targetExpr.sourceRange) << *result->type;
            return badExpr(compilation, result);
        }
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
            if (typeKey.isSimpleType()) {
                auto& expr =
                    bind(typeKey, *item->expr, item->expr->getFirstToken().location(), context);

                typeSetters.emplace(TypeSetter{ &typeKey, &expr });
                bad |= expr.bad();
            }
            else {
                context.addDiag(diag::AssignmentPatternKeyExpr, item->key->sourceRange());
                bad = true;
            }
        }
        else {
            context.addDiag(diag::AssignmentPatternKeyExpr, item->key->sourceRange());
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
            if (typeKey.isSimpleType()) {
                auto& expr =
                    bind(typeKey, *item->expr, item->expr->getFirstToken().location(), context);

                typeSetters.emplace(TypeSetter{ &typeKey, &expr });
                bad |= expr.bad();
            }
            else {
                context.addDiag(diag::AssignmentPatternKeyExpr, item->key->sourceRange());
                bad = true;
            }
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

} // namespace slang
