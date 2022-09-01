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
        if (expr.bad()) {
            if (context.cacheResults())
                expr.constant = &ConstantValue::Invalid;
            return nullptr;
        }

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
            // Ensure that we get some kind of diagnostic issued here.
            auto result = expr.eval(context);
            ASSERT(result.bad());
            return nullptr;
        }
    }

    LValue visitInvalid(const Expression&, EvalContext&) { return nullptr; }
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

struct HierarchicalVisitor {
    bool any = false;

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<Expression, T>) {
            if (expr.kind == ExpressionKind::HierarchicalValue) {
                any = true;
            }
            else if constexpr (is_detected_v<ASTDetectors::visitExprs_t, T, HierarchicalVisitor>) {
                expr.visitExprs(*this);
            }
        }
    }

    void visitInvalid(const Expression&) {}
    void visitInvalid(const AssertionExpr&) {}
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
    return selfDetermined(context.getCompilation(), syntax, context, extraFlags);
}

const Expression& Expression::bindLValue(const ExpressionSyntax& lhs, const Type& rhs,
                                         SourceLocation location, const BindContext& context,
                                         bool isInout) {
    Compilation& comp = context.getCompilation();

    // Create a placeholder expression that will carry the type of the rhs.
    // Nothing will ever actually look at this expression, it's there only
    // to fill the space in the created AssignmentExpression.
    SourceRange rhsRange{ location, location };
    auto rhsExpr = comp.emplace<EmptyArgumentExpression>(rhs, rhsRange);
    if (rhsExpr->bad())
        return badExpr(comp, nullptr);

    auto instance = context.getInstance();
    Expression* lhsExpr;
    if (lhs.kind == SyntaxKind::StreamingConcatenationExpression && !isInout &&
        (!instance || instance->arrayPath.empty())) {
        lhsExpr =
            &selfDetermined(comp, lhs, context, BindFlags::StreamingAllowed | BindFlags::LValue);
    }
    else {
        lhsExpr = &create(comp, lhs, context, BindFlags::LValue, rhsExpr->type);
    }

    selfDetermined(context, lhsExpr);

    bitmask<AssignFlags> assignFlags;
    if (instance) {
        if (isInout)
            assignFlags = AssignFlags::InOutPort;
        else if (instance->kind != SymbolKind::PrimitiveInstance)
            assignFlags = AssignFlags::OutputPort;
    }

    SourceRange lhsRange = lhs.sourceRange();
    return AssignmentExpression::fromComponents(
        comp, std::nullopt, assignFlags, *lhsExpr, *rhsExpr, lhsRange.start(),
        /* timingControl */ nullptr, lhsRange, context.resetFlags(BindFlags::OutputArg));
}

const Expression& Expression::bindRValue(const Type& lhs, const ExpressionSyntax& rhs,
                                         SourceLocation location, const BindContext& context,
                                         bitmask<BindFlags> extraFlags) {
    Compilation& comp = context.getCompilation();

    BindContext ctx = context.resetFlags(extraFlags);
    if (lhs.isVirtualInterface()) {
        if (auto ref = tryBindInterfaceRef(ctx, rhs, lhs))
            return *ref;
    }

    auto instance = context.getInstance();
    if (!instance || instance->arrayPath.empty())
        extraFlags |= BindFlags::StreamingAllowed;

    Expression& expr = create(comp, rhs, ctx, extraFlags, &lhs);
    return convertAssignment(ctx, lhs, expr, location);
}

const Expression& Expression::bindRefArg(const Type& lhs, bool isConstRef,
                                         const ExpressionSyntax& rhs, SourceLocation location,
                                         const BindContext& context) {
    Compilation& comp = context.getCompilation();
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

    // ref args are considered drivers unless they are const.
    if (!isConstRef) {
        // The check for ref-args is more strict than the check for lvalues,
        // so the net effect of this call is to get a driver registered for
        // us without duplicating the logic for determining longest static prefix.
        expr.requireLValue(context);
    }

    return expr;
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
            return bindLValue(syntax, argType, loc, context, direction == ArgumentDirection::InOut);
        case ArgumentDirection::Ref:
            return bindRefArg(argType, isConstRef, syntax, loc, context);
    }
    THROW_UNREACHABLE;
}

const Expression& Expression::bindImplicitParam(
    const DataTypeSyntax& typeSyntax, const ExpressionSyntax& rhs, SourceLocation location,
    const BindContext& exprContext, const BindContext& typeContext, bitmask<BindFlags> extraFlags) {

    Compilation& comp = exprContext.getCompilation();
    Expression& expr = create(comp, rhs, exprContext, extraFlags);
    const Type* lhsType = expr.type;

    // Rules are described in [6.20.2].
    auto& it = typeSyntax.as<ImplicitTypeSyntax>();
    if (!it.dimensions.empty()) {
        // If we have a range provided, the result is always an integral value
        // of the provided width -- getType() will do what we want here.
        lhsType = &comp.getType(typeSyntax, typeContext);
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

    return convertAssignment(exprContext, *lhsType, expr, location);
}

const Expression& Expression::bindSelector(Expression& value, const ElementSelectSyntax& syntax,
                                           const BindContext& context) {
    return bindSelector(context.getCompilation(), value, syntax, context);
}

ConstantValue Expression::eval(EvalContext& context) const {
    EvalVisitor visitor;
    return visit(visitor, context);
}

LValue Expression::evalLValue(EvalContext& context) const {
    LValueVisitor visitor;
    return visit(visitor, context);
}

optional<ConstantRange> Expression::evalSelector(EvalContext& context) const {
    ConstantValue unused1;
    bool unused2;
    switch (kind) {
        case ExpressionKind::ElementSelect:
            return as<ElementSelectExpression>().evalIndex(context, nullptr, unused1, unused2);
        case ExpressionKind::RangeSelect:
            return as<RangeSelectExpression>().evalRange(context, nullptr);
        case ExpressionKind::MemberAccess:
            return as<MemberAccessExpression>().getSelectRange();
        default:
            return {};
    }
}

bool Expression::requireLValue(const BindContext& context, SourceLocation location,
                               bitmask<AssignFlags> flags, const Expression* longestStaticPrefix,
                               EvalContext* customEvalContext) const {
    switch (kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue: {
            auto& ve = as<ValueExpressionBase>();
            return ve.requireLValueImpl(context, location, flags, longestStaticPrefix,
                                        customEvalContext);
        }
        case ExpressionKind::ElementSelect: {
            auto& select = as<ElementSelectExpression>();
            return select.requireLValueImpl(context, location, flags, longestStaticPrefix,
                                            customEvalContext);
        }
        case ExpressionKind::RangeSelect: {
            auto& select = as<RangeSelectExpression>();
            return select.requireLValueImpl(context, location, flags, longestStaticPrefix,
                                            customEvalContext);
        }
        case ExpressionKind::MemberAccess: {
            auto& access = as<MemberAccessExpression>();
            return access.requireLValueImpl(context, location, flags, longestStaticPrefix,
                                            customEvalContext);
        }
        case ExpressionKind::Concatenation: {
            auto& concat = as<ConcatenationExpression>();
            if (!concat.type->isIntegral())
                break;

            ASSERT(!longestStaticPrefix || flags.has(AssignFlags::SlicedPort));
            for (auto op : concat.operands()) {
                if (!op->requireLValue(context, location, flags | AssignFlags::InConcat, nullptr,
                                       customEvalContext)) {
                    return false;
                }
            }
            return true;
        }
        case ExpressionKind::Streaming: {
            ASSERT(!longestStaticPrefix);
            auto& stream = as<StreamingConcatenationExpression>();
            for (auto& op : stream.streams()) {
                if (!op.operand->requireLValue(context, location, flags | AssignFlags::InConcat,
                                               longestStaticPrefix, customEvalContext)) {
                    return false;
                }
            }
            return true;
        }
        case ExpressionKind::Conversion: {
            auto& conv = as<ConversionExpression>();
            if (conv.isImplicit()) {
                return conv.operand().requireLValue(context, location, flags, longestStaticPrefix,
                                                    customEvalContext);
            }
            break;
        }
        case ExpressionKind::Invalid:
            return false;
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
    auto sym = getSymbolReference(/* allowPacked */ false);
    if (!sym || !VariableSymbol::isKind(sym->kind))
        return false;

    auto& var = sym->as<VariableSymbol>();
    if (!isConstRef && var.flags.has(VariableFlags::Const) &&
        (!allowConstClassHandle || !var.getType().isClass())) {
        return false;
    }

    // Need to recursively check the left hand side of element selects and member accesses
    // to be sure this is actually an lvalue and not, for example, the result of a
    // function call or something.
    switch (kind) {
        case ExpressionKind::ElementSelect:
            return as<ElementSelectExpression>().value().canConnectToRefArg(isConstRef, false);
        case ExpressionKind::RangeSelect:
            return as<RangeSelectExpression>().value().canConnectToRefArg(isConstRef, false);
        case ExpressionKind::MemberAccess:
            return as<MemberAccessExpression>().value().canConnectToRefArg(isConstRef, true);
        default:
            return true;
    }
}

optional<bitwidth_t> Expression::getEffectiveWidth() const {
    EffectiveWidthVisitor visitor;
    return visit(visitor);
}

const Symbol* Expression::getSymbolReference(bool allowPacked) const {
    switch (kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue:
            return &as<ValueExpressionBase>().symbol;
        case ExpressionKind::ElementSelect: {
            auto& val = as<ElementSelectExpression>().value();
            return (allowPacked || val.type->isUnpackedArray()) ? val.getSymbolReference()
                                                                : nullptr;
        }
        case ExpressionKind::RangeSelect: {
            auto& val = as<RangeSelectExpression>().value();
            return (allowPacked || val.type->isUnpackedArray()) ? val.getSymbolReference()
                                                                : nullptr;
        }
        case ExpressionKind::MemberAccess: {
            auto& access = as<MemberAccessExpression>();
            auto& val = access.value();
            if (allowPacked || val.type->isClass() || val.type->isUnpackedStruct() ||
                val.type->isUnpackedUnion()) {
                return &access.member;
            }
            return nullptr;
        }
        case ExpressionKind::HierarchicalReference:
            return as<HierarchicalReferenceExpression>().symbol;
        case ExpressionKind::Conversion: {
            auto& conv = as<ConversionExpression>();
            if (conv.isImplicit())
                return conv.operand().getSymbolReference(allowPacked);
            return nullptr;
        }
        case ExpressionKind::Assignment: {
            auto& assign = as<AssignmentExpression>();
            if (assign.isLValueArg())
                return assign.left().getSymbolReference(allowPacked);
            return nullptr;
        }
        default:
            return nullptr;
    }
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
                   nv.symbol.as<ParameterSymbol>().isImplicitString(sourceRange);
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

bool Expression::hasHierarchicalReference() const {
    HierarchicalVisitor visitor;
    visit(visitor);
    return visitor.any;
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
        case SyntaxKind::WildcardLiteralExpression:
            result = &UnboundedLiteral::fromSyntax(context, syntax.as<LiteralExpressionSyntax>());
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
            if (!context.flags.has(BindFlags::NonProcedural) &&
                !context.flags.has(BindFlags::AssignmentDisallowed)) {
                extraFlags |= BindFlags::AssignmentAllowed;
            }

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

            // The syntax node might have already been assigned after creating the
            // call expression, for cases like let decls that get expanded in place.
            // Return early to avoid overwriting that syntax node.
            if (result->syntax)
                return *result;
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
        case SyntaxKind::ExpressionOrDist:
            result = &DistExpression::fromSyntax(compilation, syntax.as<ExpressionOrDistSyntax>(),
                                                 context);
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
        case SyntaxKind::TaggedUnionExpression:
            result = &TaggedUnionExpression::fromSyntax(
                compilation, syntax.as<TaggedUnionExpressionSyntax>(), context, assignmentTarget);
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
    bitmask<LookupFlags> flags = LookupFlags::None;
    if (invocation && invocation->arguments)
        flags |= LookupFlags::AllowDeclaredAfter;

    // Special case scenarios: temporary variables, class-scoped randomize calls,
    // and expanding sequences and properties.
    if (context.firstTempVar || context.randomizeDetails || context.assertionInstance) {
        // If we have any temporary variables, they need to be findable even though they aren't
        // added to any scope. Check for that case and manually look for its name here.
        if (context.firstTempVar) {
            LookupResult result;
            if (Lookup::findTempVar(*context.scope, *context.firstTempVar, syntax, result)) {
                result.reportDiags(context);
                return bindLookupResult(compilation, result, syntax.sourceRange(), invocation,
                                        withClause, context);
            }
        }

        if (context.randomizeDetails && context.randomizeDetails->classType) {
            // Inside a class-scoped randomize call, first do a lookup in the class scope.
            // If it's not found, we proceed to do a normal lookup.
            LookupResult result;
            if (Lookup::withinClassRandomize(context, syntax, flags, result)) {
                result.reportDiags(context);
                return bindLookupResult(compilation, result, syntax.sourceRange(), invocation,
                                        withClause, context);
            }
            else if (result.hasError()) {
                result.reportDiags(context);
                return badExpr(compilation, nullptr);
            }
        }

        if (context.assertionInstance) {
            // Look for a matching local assertion variable.
            LookupResult result;
            if (Lookup::findAssertionLocalVar(context, syntax, result)) {
                result.reportDiags(context);
                return bindLookupResult(compilation, result, syntax.sourceRange(), invocation,
                                        withClause, context);
            }
        }
    }

    // Normal name lookup and resolution.
    LookupResult result;
    Lookup::name(syntax, context, flags, result);
    result.reportDiags(context);

    if (result.systemSubroutine) {
        // There won't be any selectors here; this gets checked in the lookup call.
        ASSERT(result.selectors.empty());

        SourceRange callRange = invocation ? invocation->sourceRange() : syntax.sourceRange();
        CallExpression::SystemCallInfo callInfo{ result.systemSubroutine, context.scope, {} };
        return CallExpression::fromLookup(compilation, callInfo, nullptr, invocation, withClause,
                                          callRange, context);
    }

    return bindLookupResult(compilation, result, syntax.sourceRange(), invocation, withClause,
                            context);
}

Expression& Expression::bindLookupResult(Compilation& compilation, LookupResult& result,
                                         SourceRange sourceRange,
                                         const InvocationExpressionSyntax* invocation,
                                         const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                         const BindContext& context) {
    const Symbol* symbol = result.found;
    if (!symbol)
        return badExpr(compilation, nullptr);

    auto errorIfInvoke = [&]() {
        // If we require a subroutine, enforce that now. The invocation syntax will have been
        // nulled out if we used it elsewhere in this function.
        if (invocation) {
            SourceLocation loc = invocation->arguments ? invocation->arguments->openParen.location()
                                                       : sourceRange.start();
            auto& diag = context.addDiag(diag::ExpressionNotCallable, loc);
            diag << sourceRange;
            return false;
        }
        else if (withClause) {
            context.addDiag(diag::UnexpectedWithClause, withClause->with.range());
            return false;
        }
        return true;
    };

    if (context.flags.has(BindFlags::AllowDataType) && symbol->isType()) {
        // We looked up a named data type and we were allowed to do so, so return it.
        const Type& resultType = Type::fromLookupResult(compilation, result, sourceRange, context);
        auto expr = compilation.emplace<DataTypeExpression>(resultType, sourceRange);
        if (!expr->bad() && !errorIfInvoke())
            return badExpr(compilation, expr);

        return *expr;
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

    Expression* expr;
    switch (symbol->kind) {
        case SymbolKind::Subroutine: {
            ASSERT(result.selectors.empty());
            SourceRange callRange = invocation ? invocation->sourceRange() : sourceRange;
            expr = &CallExpression::fromLookup(compilation, &symbol->as<SubroutineSymbol>(),
                                               nullptr, invocation, withClause, callRange, context);
            invocation = nullptr;
            withClause = nullptr;
            break;
        }
        case SymbolKind::Sequence:
        case SymbolKind::Property:
        case SymbolKind::LetDecl: {
            const InvocationExpressionSyntax* localInvoke = nullptr;
            if (result.selectors.empty())
                localInvoke = std::exchange(invocation, nullptr);

            expr = &AssertionInstanceExpression::fromLookup(*symbol, localInvoke, sourceRange,
                                                            context);

            if (symbol->kind == SymbolKind::LetDecl && result.isHierarchical) {
                SourceRange callRange = localInvoke ? localInvoke->sourceRange() : sourceRange;
                context.addDiag(diag::LetHierarchical, callRange);
            }
            break;
        }
        case SymbolKind::AssertionPort:
            expr = &AssertionInstanceExpression::bindPort(*symbol, sourceRange, context);
            break;
        case SymbolKind::ConstraintBlock: {
            // If there are selectors then this is ok -- either they will be valid because
            // they're accessing a built-in method or they will issue an error.
            bool constraintAllowed = !result.selectors.empty();
            expr = &ValueExpressionBase::fromSymbol(context, *symbol, result.isHierarchical,
                                                    sourceRange, constraintAllowed);
            break;
        }
        default:
            expr = &ValueExpressionBase::fromSymbol(context, *symbol, result.isHierarchical,
                                                    sourceRange);
            break;
    }

    // Drill down into member accesses.
    for (size_t i = 0; i < result.selectors.size(); i++) {
        if (expr->bad())
            return *expr;

        auto& selector = result.selectors[i];
        auto memberSelect = std::get_if<LookupResult::MemberSelector>(&selector);
        if (memberSelect) {
            // If this is an access via a virtual interface we need to look at
            // all the selectors together, as this may constitute a hierarchical reference.
            if (expr->type->isVirtualInterface()) {
                LookupResult nextResult;
                span<LookupResult::Selector> selectors = result.selectors;
                Lookup::selectChild(*expr->type, expr->sourceRange, selectors.subspan(i), context,
                                    nextResult);

                nextResult.reportDiags(context);
                if (!nextResult.found)
                    return badExpr(compilation, expr);

                return bindLookupResult(compilation, nextResult, sourceRange, invocation,
                                        withClause, context);
            }

            if (i == result.selectors.size() - 1) {
                expr = &MemberAccessExpression::fromSelector(compilation, *expr, *memberSelect,
                                                             invocation, withClause, context);

                if (expr->kind == ExpressionKind::Call) {
                    invocation = nullptr;
                    withClause = nullptr;
                }
            }
            else {
                expr = &MemberAccessExpression::fromSelector(compilation, *expr, *memberSelect,
                                                             nullptr, nullptr, context);
            }
        }
        else {
            // Element / range selectors.
            auto selectSyntax = std::get<const ElementSelectSyntax*>(selector);
            expr = &bindSelector(compilation, *expr, *selectSyntax, context);
        }
    }

    if (!expr->bad() && !errorIfInvoke())
        return badExpr(compilation, expr);

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

Expression* Expression::tryBindInterfaceRef(const BindContext& context,
                                            const ExpressionSyntax& syntax,
                                            const Type& targetType) {
    const ExpressionSyntax* expr = &syntax;
    while (expr->kind == SyntaxKind::ParenthesizedExpression)
        expr = expr->as<ParenthesizedExpressionSyntax>().expression;

    if (!NameSyntax::isKind(expr->kind))
        return nullptr;

    LookupResult result;
    Lookup::name(expr->as<NameSyntax>(), context, LookupFlags::None, result);
    if (!result.found)
        return nullptr;

    auto& comp = context.getCompilation();
    auto symbol = result.found;
    if (symbol->kind == SymbolKind::InterfacePort) {
        auto& ifacePort = symbol->as<InterfacePortSymbol>();
        string_view modportName = ifacePort.modport;

        symbol = ifacePort.getConnection();
        if (symbol && !result.selectors.empty()) {
            SmallVectorSized<const ElementSelectSyntax*, 4> selectors;
            for (auto& sel : result.selectors)
                selectors.append(std::get<0>(sel));

            symbol = Lookup::selectChild(*symbol, selectors, context, result);
            if (symbol && !modportName.empty()) {
                // TODO: find modport
            }
        }

        if (!symbol) {
            // Returning nullptr from this function means to try doing normal expression
            // binding, but if we hit this case here we found the iface and simply failed
            // to connect it, likely because we're in an uninstantiated context. Return
            // a badExpr here to silence any follow on errors that might otherwise result.
            return &badExpr(comp, nullptr);
        }

        result.reportDiags(context);
    }
    else if ((symbol->kind == SymbolKind::Instance && symbol->as<InstanceSymbol>().isInterface()) ||
             symbol->kind == SymbolKind::Modport) {
        result.reportDiags(context);
        result.errorIfSelectors(context);
    }
    else {
        return nullptr;
    }

    const InstanceBodySymbol* iface = nullptr;
    const ModportSymbol* modport = nullptr;
    if (symbol->kind == SymbolKind::Modport) {
        modport = &symbol->as<ModportSymbol>();
        iface = &modport->getParentScope()->asSymbol().as<InstanceBodySymbol>();
    }
    else {
        iface = &symbol->as<InstanceSymbol>().body;
    }

    // Now make sure the interface or modport we found matches the target type.
    auto& vit = targetType.getCanonicalType().as<VirtualInterfaceType>();
    if (&vit.iface != iface->parentInstance) {
        // TODO: error
    }
    else if (modport && vit.modport != modport) {
        // TODO: error
    }

    return comp.emplace<HierarchicalReferenceExpression>(*symbol, targetType, syntax.sourceRange());
}

void Expression::findPotentiallyImplicitNets(const SyntaxNode& expr, const BindContext& context,
                                             SmallVector<Token>& results) {
    struct Visitor : public SyntaxVisitor<Visitor> {
        Visitor(const BindContext& context, SmallVector<Token>& results) :
            context(context), results(results) {}

        void handle(const NameSyntax& nameSyntax) {
            if (nameSyntax.kind != SyntaxKind::IdentifierName)
                return;

            LookupResult result;
            BindContext ctx(*context.scope, LookupLocation::max);
            Lookup::name(nameSyntax, ctx, LookupFlags::NoUndeclaredError, result);

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
