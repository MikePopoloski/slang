//------------------------------------------------------------------------------
// Expression.cpp
// Expression creation and analysis
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Expression.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/types/Type.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/syntax/SyntaxVisitor.h"

namespace {

using namespace slang;
using namespace slang::ast;

struct EvalVisitor {
    template<typename T>
    ConstantValue visit(const T& expr, EvalContext& context) {
        if (expr.constant)
            return *expr.constant;

        if (expr.bad()) {
            if (context.cacheResults())
                expr.constant = &ConstantValue::Invalid;
            return nullptr;
        }

        ConstantValue cv = expr.evalImpl(context);
        if (cv && context.cacheResults()) {
            // If we're caching results we can't let any reported
            // diagnostics get lost because there won't be another
            // opportunity to see them, so make sure they get logged
            // to the compilation now.
            context.reportWarnings();
            expr.constant = context.getCompilation().allocConstant(std::move(cv));
            return *expr.constant;
        }

        return cv;
    }
};

class LValueVisitor {
public:
    template<typename T>
    LValue visit(const T& expr, EvalContext& context) {
        if constexpr (requires { expr.evalLValueImpl(context); }) {
            if (expr.bad())
                return nullptr;

            return expr.evalLValueImpl(context);
        }
        else {
            // Ensure that we get some kind of diagnostic issued here.
            auto result = expr.eval(context);
            SLANG_ASSERT(result.bad());
            return nullptr;
        }
    }
};

class EffectiveWidthVisitor {
public:
    template<typename T>
    std::optional<bitwidth_t> visit(const T& expr) {
        if constexpr (requires { expr.getEffectiveWidthImpl(); }) {
            if (expr.bad())
                return std::nullopt;

            return expr.getEffectiveWidthImpl();
        }
        else {
            return expr.type->getBitWidth();
        }
    }
};

class EffectiveSignVisitor {
public:
    using EffectiveSign = Expression::EffectiveSign;

    bool isForConversion;

    explicit EffectiveSignVisitor(bool isForConversion) : isForConversion(isForConversion) {}

    template<typename T>
    EffectiveSign visit(const T& expr) {
        if constexpr (requires { expr.getEffectiveSignImpl(isForConversion); }) {
            if (expr.bad())
                return EffectiveSign::Either;

            return expr.getEffectiveSignImpl(isForConversion);
        }
        else {
            return expr.type->isSigned() ? EffectiveSign::Signed : EffectiveSign::Unsigned;
        }
    }
};

struct HierarchicalVisitor {
    bool any = false;

    template<typename T>
    void visit(const T& expr) {
        if constexpr (std::is_base_of_v<Expression, T>) {
            if (expr.kind == ExpressionKind::HierarchicalValue) {
                any = true;
            }
            else if constexpr (HasVisitExprs<T, HierarchicalVisitor>) {
                expr.visitExprs(*this);
            }
        }
    }
};

} // namespace

namespace slang::ast {

using namespace parsing;
using namespace syntax;

// This visitor handles inserting implicit conversions into an expression
// tree where necessary. SystemVerilog has an additional weird feature where
// the type of one branch of an expression tree can bubble up and then propagate
// back down a different branch, which is also implemented here.
struct Expression::PropagationVisitor {
    const ASTContext& context;
    const Type& newType;
    const Expression* parentExpr;
    SourceRange opRange;
    ConversionKind conversionKind;

    PropagationVisitor(const ASTContext& context, const Type& newType, const Expression* parentExpr,
                       SourceRange opRange, ConversionKind conversionKind) :
        context(context), newType(newType), parentExpr(parentExpr), opRange(opRange),
        conversionKind(conversionKind) {}

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
        if constexpr (requires { expr.propagateType(context, newType, opRange, conversionKind); }) {
            if ((newType.isFloating() && expr.type->isFloating()) ||
                (newType.isIntegral() && expr.type->isIntegral()) || newType.isString() ||
                expr.kind == ExpressionKind::ValueRange) {

                if (!needConversion) {
                    // If we don't need a conversion here we still need to call propagateType as
                    // one of our child expressions may still need conversion. However, we shouldn't
                    // pass along our given opRange since we didn't need the conversion here, so our
                    // parent operator isn't relevant. We should try to refigure an opRange for our
                    // most immediate parent expression instead.
                    updateRange(expr);
                }

                if (expr.propagateType(context, newType, opRange, conversionKind)) {
                    // We propagated the type successfully so we don't need a conversion.
                    // We should however clear out any constant value that may have been
                    // stored here, since it may no longer be valid given the new type.
                    needConversion = false;
                    expr.constant = nullptr;
                }
            }
        }

        Expression* result = &expr;
        if (needConversion) {
            result = &ConversionExpression::makeImplicit(context, newType, conversionKind, expr,
                                                         parentExpr, opRange);
        }

        return *result;
    }

private:
    void updateRange(const Expression& expr) {
        opRange = {};
        switch (expr.kind) {
            case ExpressionKind::BinaryOp:
                opRange = expr.as<BinaryExpression>().opRange;
                break;
            case ExpressionKind::ConditionalOp: {
                auto opLoc = expr.as<ConditionalExpression>().opLoc;
                opRange = {opLoc, opLoc + 1};
                break;
            }
            default:
                break;
        }
    }
};

const InvalidExpression InvalidExpression::Instance(nullptr, ErrorType::Instance);

const Expression& Expression::bind(const ExpressionSyntax& syntax, const ASTContext& context,
                                   bitmask<ASTFlags> extraFlags) {
    return selfDetermined(context.getCompilation(), syntax, context, context.flags | extraFlags);
}

const Expression& Expression::bindLValue(const ExpressionSyntax& lhs, const Type& rhs,
                                         SourceLocation location, const ASTContext& context,
                                         bool isInout) {
    Compilation& comp = context.getCompilation();

    // Create a placeholder expression that will carry the type of the rhs.
    // Nothing will ever actually look at this expression, it's there only
    // to fill the space in the created AssignmentExpression.
    auto rhsExpr = comp.emplace<EmptyArgumentExpression>(rhs, SourceRange{location, location});

    auto instance = context.getInstance();
    Expression* lhsExpr;
    if (lhs.kind == SyntaxKind::StreamingConcatenationExpression && !isInout &&
        (!instance || instance->arrayPath.empty())) {
        lhsExpr = &selfDetermined(comp, lhs, context,
                                  ASTFlags::StreamingAllowed | ASTFlags::LValue);
    }
    else {
        bitmask<ASTFlags> astFlags = ASTFlags::LValue;
        if (isInout)
            astFlags |= ASTFlags::LAndRValue;

        lhsExpr = &create(comp, lhs, context, astFlags, rhsExpr->type);
        selfDetermined(context, lhsExpr);
    }

    bitmask<AssignFlags> assignFlags;
    if (instance) {
        if (isInout)
            assignFlags = AssignFlags::InOutPort;
        else if (instance->kind != SymbolKind::PrimitiveInstance)
            assignFlags = AssignFlags::OutputPort;
    }

    bitmask<ASTFlags> astFlags = ASTFlags::OutputArg;
    if (context.flags.has(ASTFlags::NotADriver))
        astFlags |= ASTFlags::NotADriver;

    SourceRange lhsRange = lhs.sourceRange();
    return AssignmentExpression::fromComponents(comp, std::nullopt, assignFlags, *lhsExpr, *rhsExpr,
                                                lhsRange, /* timingControl */ nullptr, lhsRange,
                                                context.resetFlags(astFlags));
}

const Expression& Expression::bindLValue(const ExpressionSyntax& syntax, const ASTContext& context,
                                         bitmask<AssignFlags> assignFlags) {
    auto& expr = bind(syntax, context, ASTFlags::LValue);
    if (!expr.requireLValue(context, {}, assignFlags))
        return badExpr(context.getCompilation(), &expr);
    return expr;
}

const Expression& Expression::bindRValue(const Type& lhs, const ExpressionSyntax& rhs,
                                         SourceRange assignmentRange, const ASTContext& context,
                                         bitmask<ASTFlags> extraFlags) {
    Compilation& comp = context.getCompilation();

    ASTContext ctx = context.resetFlags(extraFlags);
    if (lhs.isVirtualInterfaceOrArray()) {
        if (auto ref = tryBindInterfaceRef(ctx, rhs, /* isInterfacePort */ false)) {
            if (!assignmentRange.start())
                assignmentRange = ref->sourceRange;
            return convertAssignment(ctx, lhs, *ref, assignmentRange);
        }
    }

    auto instance = context.getInstance();
    if (!instance || instance->arrayPath.empty())
        extraFlags |= ASTFlags::StreamingAllowed;

    Expression& expr = create(comp, rhs, ctx, extraFlags, &lhs);
    if (!assignmentRange.start())
        assignmentRange = expr.sourceRange;

    return convertAssignment(ctx, lhs, expr, assignmentRange);
}

static bool canConnectToRefArg(const ASTContext& context, const Expression& expr,
                               bitmask<VariableFlags> argFlags, bool allowConstClassHandle = false,
                               bool disallowDynamicArrays = false) {
    auto sym = expr.getSymbolReference(/* allowPacked */ false);
    if (!sym || !VariableSymbol::isKind(sym->kind))
        return false;

    auto& var = sym->as<VariableSymbol>();
    if (!argFlags.has(VariableFlags::Const) && var.flags.has(VariableFlags::Const) &&
        (!allowConstClassHandle || !var.getType().isClass())) {
        return false;
    }

    const bool isRefStatic = argFlags.has(VariableFlags::RefStatic);
    if (isRefStatic) {
        if (var.lifetime == VariableLifetime::Automatic &&
            !var.flags.has(VariableFlags::RefStatic)) {
            return false;
        }

        if (disallowDynamicArrays && var.getType().isDynamicallySizedArray())
            return false;
    }

    // Need to recursively check the left hand side of element selects and member accesses
    // to be sure this is actually an lvalue and not, for example, the result of a
    // function call or something.
    switch (expr.kind) {
        case ExpressionKind::ElementSelect:
            return canConnectToRefArg(context, expr.as<ElementSelectExpression>().value(), argFlags,
                                      false, isRefStatic);
        case ExpressionKind::RangeSelect:
            return canConnectToRefArg(context, expr.as<RangeSelectExpression>().value(), argFlags,
                                      false, isRefStatic);
        case ExpressionKind::MemberAccess:
            return canConnectToRefArg(context, expr.as<MemberAccessExpression>().value(), argFlags,
                                      true);
        default:
            return true;
    }
}

const Expression& Expression::bindRefArg(const Type& lhs, bitmask<VariableFlags> argFlags,
                                         const ExpressionSyntax& rhs, SourceLocation location,
                                         const ASTContext& context) {
    Compilation& comp = context.getCompilation();
    Expression& expr = selfDetermined(comp, rhs, context);
    if (expr.bad())
        return expr;

    if (lhs.isError())
        return badExpr(comp, &expr);

    const bool isConstRef = argFlags.has(VariableFlags::Const);
    if (!canConnectToRefArg(context, expr, argFlags)) {
        DiagCode code = diag::InvalidRefArg;
        if (!isConstRef && canConnectToRefArg(context, expr, argFlags | VariableFlags::Const)) {
            // If we can't bind to ref but we can bind to 'const ref', issue a more
            // specific error about constness.
            code = diag::ConstVarToRef;
        }
        else if (argFlags.has(VariableFlags::RefStatic) &&
                 canConnectToRefArg(context, expr, argFlags & ~VariableFlags::RefStatic)) {
            // Same idea, but for ref static restrictions.
            code = diag::AutoVarToRefStatic;
        }

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
        if (auto sym = expr.getSymbolReference())
            comp.noteReference(*sym, /* isLValue */ true);
    }

    return expr;
}

const Expression& Expression::bindArgument(const Type& argType, ArgumentDirection direction,
                                           bitmask<VariableFlags> argFlags,
                                           const ExpressionSyntax& syntax,
                                           const ASTContext& context) {
    switch (direction) {
        case ArgumentDirection::In:
            return bindRValue(argType, syntax, {}, context);
        case ArgumentDirection::Out:
        case ArgumentDirection::InOut:
            return bindLValue(syntax, argType, syntax.getFirstToken().location(), context,
                              direction == ArgumentDirection::InOut);
        case ArgumentDirection::Ref:
            return bindRefArg(argType, argFlags, syntax, syntax.getFirstToken().location(),
                              context);
    }
    SLANG_UNREACHABLE;
}

bool Expression::checkConnectionDirection(const Expression& expr, ArgumentDirection direction,
                                          const ASTContext& context, SourceLocation loc,
                                          bitmask<AssignFlags> flags) {
    switch (direction) {
        case ArgumentDirection::In:
            // All expressions are fine for inputs.
            return true;
        case ArgumentDirection::Out:
            return expr.requireLValue(context, loc, flags);
        case ArgumentDirection::InOut:
            return expr.requireLValue(context, loc, flags | AssignFlags::InOutPort);
        case ArgumentDirection::Ref:
            if (!canConnectToRefArg(context, expr, VariableFlags::None)) {
                context.addDiag(diag::InvalidRefArg, loc) << expr.sourceRange;
                return false;
            }
            return true;
    }
    SLANG_UNREACHABLE;
}

std::tuple<const Expression*, const Type*> Expression::bindImplicitParam(
    const DataTypeSyntax& typeSyntax, const ExpressionSyntax& rhs, SourceRange assignmentRange,
    const ASTContext& exprContext, const ASTContext& typeContext, bitmask<ASTFlags> extraFlags) {

    // Rules are described in [6.20.2].
    Compilation& comp = exprContext.getCompilation();
    auto& it = typeSyntax.as<ImplicitTypeSyntax>();
    if (!it.dimensions.empty()) {
        // If we have a range provided, the result is always an integral value
        // of the provided width -- getType() will do what we want here.
        auto lhsType = &comp.getType(typeSyntax, typeContext);
        return {&bindRValue(*lhsType, rhs, assignmentRange, exprContext, extraFlags), lhsType};
    }

    Expression& expr = create(comp, rhs, exprContext, extraFlags);
    const Type* lhsType = expr.type;
    if (it.signing) {
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
                bits = std::max(bits, 32u);

            // Keep the signed flag but force four state.
            auto flags = lhsType->getIntegralFlags();
            flags |= IntegralFlags::FourState;

            lhsType = &comp.getType(bits, flags);
        }
    }

    return {&convertAssignment(exprContext, *lhsType, expr, assignmentRange), lhsType};
}

const Expression& Expression::bindSelector(Expression& value, const ElementSelectSyntax& syntax,
                                           const ASTContext& context) {
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

std::optional<ConstantRange> Expression::evalSelector(EvalContext& context,
                                                      bool enforceBounds) const {
    ConstantValue unused1;
    bool unused2;
    switch (kind) {
        case ExpressionKind::ElementSelect:
            return as<ElementSelectExpression>().evalIndex(context, nullptr, unused1, unused2);
        case ExpressionKind::RangeSelect:
            return as<RangeSelectExpression>().evalRange(context, nullptr, enforceBounds);
        default:
            return {};
    }
}

bool Expression::requireLValue(const ASTContext& context, SourceLocation location,
                               bitmask<AssignFlags> flags,
                               const Expression* longestStaticPrefix) const {
    switch (kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue: {
            auto& ve = as<ValueExpressionBase>();
            return ve.requireLValueImpl(context, location, flags, longestStaticPrefix);
        }
        case ExpressionKind::ElementSelect: {
            auto& select = as<ElementSelectExpression>();
            return select.requireLValueImpl(context, location, flags, longestStaticPrefix);
        }
        case ExpressionKind::RangeSelect: {
            auto& select = as<RangeSelectExpression>();
            return select.requireLValueImpl(context, location, flags, longestStaticPrefix);
        }
        case ExpressionKind::MemberAccess: {
            auto& access = as<MemberAccessExpression>();
            return access.requireLValueImpl(context, location, flags, longestStaticPrefix);
        }
        case ExpressionKind::Concatenation: {
            auto& concat = as<ConcatenationExpression>();
            if (!concat.type->isIntegral())
                break;

            SLANG_ASSERT(!longestStaticPrefix || flags.has(AssignFlags::SlicedPort));
            for (auto op : concat.operands()) {
                if (!op->requireLValue(context, location, flags | AssignFlags::InConcat)) {
                    return false;
                }
            }
            return true;
        }
        case ExpressionKind::SimpleAssignmentPattern:
            return as<SimpleAssignmentPatternExpression>().isLValue;
        case ExpressionKind::Streaming: {
            SLANG_ASSERT(!longestStaticPrefix);
            auto& stream = as<StreamingConcatenationExpression>();
            for (auto& op : stream.streams()) {
                if (!op.operand->requireLValue(context, location, flags | AssignFlags::InConcat,
                                               longestStaticPrefix)) {
                    return false;
                }
            }
            return true;
        }
        case ExpressionKind::Conversion: {
            auto& conv = as<ConversionExpression>();
            if (conv.isImplicit()) {
                return conv.operand().requireLValue(context, location, flags, longestStaticPrefix);
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

void Expression::getLongestStaticPrefixes(
    SmallVector<std::pair<const ValueSymbol*, const Expression*>>& results,
    EvalContext& evalContext, const Expression* longestStaticPrefix) const {

    switch (kind) {
        case ExpressionKind::NamedValue:
        case ExpressionKind::HierarchicalValue: {
            auto& ve = as<ValueExpressionBase>();
            ve.getLongestStaticPrefixesImpl(results, longestStaticPrefix);
            break;
        }
        case ExpressionKind::ElementSelect: {
            auto& select = as<ElementSelectExpression>();
            select.getLongestStaticPrefixesImpl(results, evalContext, longestStaticPrefix);
            break;
        }
        case ExpressionKind::RangeSelect: {
            auto& select = as<RangeSelectExpression>();
            select.getLongestStaticPrefixesImpl(results, evalContext, longestStaticPrefix);
            break;
        }
        case ExpressionKind::MemberAccess: {
            auto& access = as<MemberAccessExpression>();
            access.getLongestStaticPrefixesImpl(results, evalContext, longestStaticPrefix);
            break;
        }
        case ExpressionKind::Concatenation: {
            auto& concat = as<ConcatenationExpression>();
            if (concat.type->isIntegral()) {
                for (auto op : concat.operands())
                    op->getLongestStaticPrefixes(results, evalContext, nullptr);
            }
            break;
        }
        case ExpressionKind::Streaming: {
            SLANG_ASSERT(!longestStaticPrefix);
            auto& stream = as<StreamingConcatenationExpression>();
            for (auto& op : stream.streams())
                op.operand->getLongestStaticPrefixes(results, evalContext, nullptr);
            break;
        }
        case ExpressionKind::Conversion: {
            auto& conv = as<ConversionExpression>();
            if (conv.isImplicit())
                conv.operand().getLongestStaticPrefixes(results, evalContext, longestStaticPrefix);
            break;
        }
        case ExpressionKind::Invalid:
        default:
            break;
    }
}

std::optional<bitwidth_t> Expression::getEffectiveWidth() const {
    EffectiveWidthVisitor visitor;
    return visit(visitor);
}

Expression::EffectiveSign Expression::getEffectiveSign(bool isForConversion) const {
    EffectiveSignVisitor visitor(isForConversion);
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
        case ExpressionKind::ArbitrarySymbol:
            return as<ArbitrarySymbolExpression>().symbol;
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
        case ExpressionKind::ValueRange: {
            auto& range = as<ValueRangeExpression>();
            return range.left().isImplicitString() ||
                   (range.rangeKind == ValueRangeKind::Simple && range.right().isImplicitString());
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

bool Expression::isParenthesized() const {
    return syntax && syntax->kind == SyntaxKind::ParenthesizedExpression;
}

const Expression& Expression::unwrapImplicitConversions() const {
    auto expr = this;
    while (expr->kind == ExpressionKind::Conversion) {
        auto& conv = expr->as<ConversionExpression>();
        if (!conv.isImplicit())
            break;

        expr = &conv.operand();
    }
    return *expr;
}

Expression& Expression::create(Compilation& compilation, const ExpressionSyntax& syntax,
                               const ASTContext& ctx, bitmask<ASTFlags> extraFlags,
                               const Type* assignmentTarget) {
    ASTContext context = ctx.resetFlags(extraFlags);
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
            result = &StringLiteral::fromSyntax(context, syntax.as<LiteralExpressionSyntax>());
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
            if (!context.flags.has(ASTFlags::NonProcedural) &&
                !context.flags.has(ASTFlags::AssignmentDisallowed)) {
                extraFlags |= ASTFlags::AssignmentAllowed;
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
            result = &UnaryExpression::fromSyntax(compilation,
                                                  syntax.as<PrefixUnaryExpressionSyntax>(),
                                                  context);
            break;
        case SyntaxKind::PostincrementExpression:
        case SyntaxKind::PostdecrementExpression:
            result = &UnaryExpression::fromSyntax(compilation,
                                                  syntax.as<PostfixUnaryExpressionSyntax>(),
                                                  context);
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
            result = &AssignmentExpression::fromSyntax(compilation,
                                                       syntax.as<BinaryExpressionSyntax>(),
                                                       context);
            break;
        case SyntaxKind::InvocationExpression:
            result = &CallExpression::fromSyntax(compilation,
                                                 syntax.as<InvocationExpressionSyntax>(), nullptr,
                                                 context);

            // The syntax node might have already been assigned after creating the
            // call expression, for cases like let decls that get expanded in place.
            // Return early to avoid overwriting that syntax node.
            if (result->syntax)
                return *result;
            break;
        case SyntaxKind::ConditionalExpression:
            result = &ConditionalExpression::fromSyntax(compilation,
                                                        syntax.as<ConditionalExpressionSyntax>(),
                                                        context, assignmentTarget);
            break;
        case SyntaxKind::InsideExpression:
            result = &InsideExpression::fromSyntax(compilation, syntax.as<InsideExpressionSyntax>(),
                                                   context);
            break;
        case SyntaxKind::MemberAccessExpression:
            result = &MemberAccessExpression::fromSyntax(compilation,
                                                         syntax.as<MemberAccessExpressionSyntax>(),
                                                         nullptr, nullptr, context);
            break;
        case SyntaxKind::ConcatenationExpression:
            result = &ConcatenationExpression::fromSyntax(
                compilation, syntax.as<ConcatenationExpressionSyntax>(), context, assignmentTarget);
            break;
        case SyntaxKind::EmptyQueueExpression:
            result = &ConcatenationExpression::fromEmpty(compilation,
                                                         syntax.as<EmptyQueueExpressionSyntax>(),
                                                         context, assignmentTarget);
            break;
        case SyntaxKind::MultipleConcatenationExpression:
            result = &ReplicationExpression::fromSyntax(
                compilation, syntax.as<MultipleConcatenationExpressionSyntax>(), context);
            break;
        case SyntaxKind::StreamingConcatenationExpression:
            result = &StreamingConcatenationExpression::fromSyntax(
                compilation, syntax.as<StreamingConcatenationExpressionSyntax>(), context);
            break;
        case SyntaxKind::ElementSelectExpression:
            result = &bindSelectExpression(compilation, syntax.as<ElementSelectExpressionSyntax>(),
                                           context);
            break;
        case SyntaxKind::CastExpression:
            result = &ConversionExpression::fromSyntax(compilation,
                                                       syntax.as<CastExpressionSyntax>(), context,
                                                       assignmentTarget);
            break;
        case SyntaxKind::SignedCastExpression:
            result = &ConversionExpression::fromSyntax(compilation,
                                                       syntax.as<SignedCastExpressionSyntax>(),
                                                       context);
            break;
        case SyntaxKind::AssignmentPatternExpression:
            result = &bindAssignmentPattern(compilation,
                                            syntax.as<AssignmentPatternExpressionSyntax>(), context,
                                            assignmentTarget);
            break;
        case SyntaxKind::ValueRangeExpression:
            result = &ValueRangeExpression::fromSyntax(compilation,
                                                       syntax.as<ValueRangeExpressionSyntax>(),
                                                       context);
            break;
        case SyntaxKind::ExpressionOrDist:
            result = &DistExpression::fromSyntax(compilation, syntax.as<ExpressionOrDistSyntax>(),
                                                 context);
            break;
        case SyntaxKind::TimingControlExpression:
            // Valid cases of this expression type are handled in AssignmentExpression.
            // If we reach this block here, the expression is invalid so always report
            // an error.
            context.addDiag(diag::TimingControlNotAllowed, syntax.sourceRange());
            result = &badExpr(compilation, nullptr);
            break;
        case SyntaxKind::NewArrayExpression:
            result = &NewArrayExpression::fromSyntax(compilation,
                                                     syntax.as<NewArrayExpressionSyntax>(), context,
                                                     assignmentTarget);
            break;
        case SyntaxKind::NewClassExpression:
            result = &NewClassExpression::fromSyntax(compilation,
                                                     syntax.as<NewClassExpressionSyntax>(), context,
                                                     assignmentTarget);
            break;
        case SyntaxKind::SuperNewDefaultedArgsExpression:
            result = &NewClassExpression::fromSyntax(
                compilation, syntax.as<SuperNewDefaultedArgsExpressionSyntax>(), context,
                assignmentTarget);
            break;
        case SyntaxKind::CopyClassExpression:
            result = &CopyClassExpression::fromSyntax(compilation,
                                                      syntax.as<CopyClassExpressionSyntax>(),
                                                      context);
            break;
        case SyntaxKind::DefaultPatternKeyExpression:
            // This should not be reachable from any valid expression creation.
            context.addDiag(diag::ExpectedExpression, syntax.sourceRange());
            result = &badExpr(compilation, nullptr);
            break;
        case SyntaxKind::MinTypMaxExpression:
            result = &MinTypMaxExpression::fromSyntax(compilation,
                                                      syntax.as<MinTypMaxExpressionSyntax>(),
                                                      context, assignmentTarget);
            break;
        case SyntaxKind::ArrayOrRandomizeMethodExpression:
            result = &CallExpression::fromSyntax(
                compilation, syntax.as<ArrayOrRandomizeMethodExpressionSyntax>(), context);
            break;
        case SyntaxKind::TaggedUnionExpression:
            result = &TaggedUnionExpression::fromSyntax(compilation,
                                                        syntax.as<TaggedUnionExpressionSyntax>(),
                                                        context, assignmentTarget);
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
            SLANG_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

Expression& Expression::bindName(Compilation& comp, const NameSyntax& syntax,
                                 const InvocationExpressionSyntax* invocation,
                                 const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                 const ASTContext& context) {
    bitmask<LookupFlags> flags = LookupFlags::None;
    if ((invocation && invocation->arguments) ||
        comp.hasFlag(CompilationFlags::AllowUseBeforeDeclare)) {
        flags |= LookupFlags::AllowDeclaredAfter;
    }

    if (context.flags.has(ASTFlags::StaticInitializer))
        flags |= LookupFlags::StaticInitializer;

    if (context.flags.has(ASTFlags::BindInstantiation))
        flags |= LookupFlags::DisallowWildcardImport | LookupFlags::DisallowUnitReferences;

    if (context.flags.has(ASTFlags::TypeOperator) &&
        comp.languageVersion() >= LanguageVersion::v1800_2023) {
        // v1800-2023: Type operator expressions are allowed to reference
        // incomplete forward class types now.
        flags |= LookupFlags::AllowIncompleteForwardTypedefs | LookupFlags::TypeReference;
    }

    // Special case scenarios: temporary variables, class-scoped randomize calls,
    // and expanding sequences and properties.
    if (context.firstTempVar || context.randomizeDetails || context.assertionInstance) {
        // If we have any temporary variables, they need to be findable even though they aren't
        // added to any scope. Check for that case and manually look for its name here.
        if (context.firstTempVar) {
            LookupResult result;
            if (Lookup::findTempVar(*context.scope, *context.firstTempVar, syntax, result)) {
                result.reportDiags(context);
                return bindLookupResult(comp, result, syntax.sourceRange(), invocation, withClause,
                                        context);
            }
        }

        if (context.randomizeDetails && context.randomizeDetails->classType) {
            // Inside a class-scoped randomize call, first do a lookup in the class scope.
            // If it's not found, we proceed to do a normal lookup.
            LookupResult result;
            if (Lookup::withinClassRandomize(context, syntax, flags, result)) {
                result.reportDiags(context);
                return bindLookupResult(comp, result, syntax.sourceRange(), invocation, withClause,
                                        context);
            }
            else if (result.hasError()) {
                result.reportDiags(context);
                return badExpr(comp, nullptr);
            }
        }

        if (context.assertionInstance) {
            // Look for a matching local assertion variable.
            LookupResult result;
            if (Lookup::findAssertionLocalVar(context, syntax, result)) {
                result.reportDiags(context);
                return bindLookupResult(comp, result, syntax.sourceRange(), invocation, withClause,
                                        context);
            }
        }
    }

    // Normal name lookup and resolution.
    LookupResult result;
    Lookup::name(syntax, context, flags, result);
    result.reportDiags(context);

    if (result.systemSubroutine) {
        // There won't be any selectors here; this gets checked in the lookup call.
        SLANG_ASSERT(result.selectors.empty());

        SourceRange callRange = invocation ? invocation->sourceRange() : syntax.sourceRange();
        CallExpression::SystemCallInfo callInfo{result.systemSubroutine, context.scope, {}};
        return CallExpression::fromLookup(comp, callInfo, nullptr, invocation, withClause,
                                          callRange, context);
    }

    return bindLookupResult(comp, result, syntax.sourceRange(), invocation, withClause, context);
}

Expression& Expression::bindLookupResult(Compilation& comp, LookupResult& result,
                                         SourceRange sourceRange,
                                         const InvocationExpressionSyntax* invocation,
                                         const ArrayOrRandomizeMethodExpressionSyntax* withClause,
                                         const ASTContext& context) {
    const Symbol* symbol = result.found;
    if (!symbol)
        return badExpr(comp, nullptr);

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

    if (context.flags.has(ASTFlags::AllowDataType) && symbol->isType()) {
        // We looked up a named data type and we were allowed to do so, so return it.
        const Type& resultType = Type::fromLookupResult(comp, result, sourceRange, context);
        auto expr = comp.emplace<DataTypeExpression>(resultType, sourceRange);
        if (!expr->bad() && !errorIfInvoke())
            return badExpr(comp, expr);

        return *expr;
    }

    // If we've found a function's return value variable and have parentheses for
    // a call expression, translate that symbol to be the subroutine itself to
    // allow for recursive function calls.
    if (symbol->kind == SymbolKind::Variable && result.selectors.empty() &&
        symbol->as<VariableSymbol>().flags.has(VariableFlags::CompilerGenerated)) {

        auto scope = symbol->getParentScope();
        if (scope && (invocation || (context.flags.has(ASTFlags::TopLevelStatement) &&
                                     comp.hasFlag(CompilationFlags::AllowRecursiveImplicitCall)))) {
            auto& sym = scope->asSymbol();
            if (sym.kind == SymbolKind::Subroutine &&
                sym.as<SubroutineSymbol>().returnValVar == symbol) {
                SLANG_ASSERT(sym.as<SubroutineSymbol>().subroutineKind == SubroutineKind::Function);
                symbol = &sym;
            }
        }
    }

    Expression* expr;
    switch (symbol->kind) {
        case SymbolKind::Subroutine: {
            SLANG_ASSERT(result.selectors.empty());
            SourceRange callRange = invocation ? invocation->sourceRange() : sourceRange;
            expr = &CallExpression::fromLookup(comp, &symbol->as<SubroutineSymbol>(), nullptr,
                                               invocation, withClause, callRange, context);
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

            if (symbol->kind == SymbolKind::LetDecl &&
                result.flags.has(LookupResultFlags::IsHierarchical)) {
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
            const bool constraintAllowed = !result.selectors.empty();
            auto hierRef = HierarchicalReference::fromLookup(comp, result);
            expr = &ValueExpressionBase::fromSymbol(context, *symbol, &hierRef, sourceRange,
                                                    constraintAllowed);
            break;
        }
        default: {
            const bool isDottedAccess =
                context.flags.has(ASTFlags::LValue) && !result.selectors.empty() &&
                std::get_if<LookupResult::MemberSelector>(&result.selectors[0]) != nullptr;

            auto hierRef = HierarchicalReference::fromLookup(comp, result);
            expr = &ValueExpressionBase::fromSymbol(context, *symbol, &hierRef, sourceRange,
                                                    /* constraintAllowed */ false, isDottedAccess);
            break;
        }
    }

    // Drill down into member accesses.
    for (size_t i = 0; i < result.selectors.size(); i++) {
        auto& selector = result.selectors[i];
        auto memberSelect = std::get_if<LookupResult::MemberSelector>(&selector);
        if (memberSelect) {
            // If this is an access via a virtual interface we need to look at
            // all the selectors together, as this may constitute a hierarchical reference.
            if (expr->type->isVirtualInterface()) {
                LookupResult nextResult;
                std::span<LookupResult::Selector> selectors = result.selectors;
                Lookup::selectChild(*expr->type, expr->sourceRange, selectors.subspan(i), context,
                                    nextResult);

                nextResult.reportDiags(context);
                if (!nextResult.found)
                    return badExpr(comp, expr);

                return bindLookupResult(comp, nextResult, sourceRange, invocation, withClause,
                                        context);
            }

            if (i == result.selectors.size() - 1) {
                expr = &MemberAccessExpression::fromSelector(comp, *expr, *memberSelect, invocation,
                                                             withClause, context,
                                                             /* isFromLookupChain */ true);

                if (expr->kind == ExpressionKind::Call) {
                    invocation = nullptr;
                    withClause = nullptr;
                }
            }
            else {
                expr = &MemberAccessExpression::fromSelector(comp, *expr, *memberSelect, nullptr,
                                                             nullptr, context,
                                                             /* isFromLookupChain */ true);
            }
        }
        else {
            // Element / range selectors.
            auto selectSyntax = std::get<const ElementSelectSyntax*>(selector);
            expr = &bindSelector(comp, *expr, *selectSyntax, context);
        }
    }

    if (!expr->bad() && !errorIfInvoke())
        return badExpr(comp, expr);

    return *expr;
}

Expression& Expression::bindSelectExpression(Compilation& compilation,
                                             const ElementSelectExpressionSyntax& syntax,
                                             const ASTContext& context) {
    Expression& value = create(compilation, *syntax.left, context);
    return bindSelector(compilation, value, *syntax.select, context);
}

Expression& Expression::bindSelector(Compilation& compilation, Expression& value,
                                     const ElementSelectSyntax& syntax, const ASTContext& context) {
    const SelectorSyntax* selector = syntax.selector;
    if (!selector) {
        context.addDiag(diag::ExpectedExpression, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    if (value.kind == ExpressionKind::RangeSelect) {
        context.addDiag(diag::SelectAfterRangeSelect, syntax.sourceRange()) << value.sourceRange;
        return badExpr(compilation, nullptr);
    }

    // The full source range of the expression includes the value and the selector syntax.
    SourceRange fullRange = {value.sourceRange.start(), syntax.sourceRange().end()};

    switch (selector->kind) {
        case SyntaxKind::BitSelect:
            return ElementSelectExpression::fromSyntax(compilation, value,
                                                       *selector->as<BitSelectSyntax>().expr,
                                                       fullRange, context);
        case SyntaxKind::SimpleRangeSelect:
        case SyntaxKind::AscendingRangeSelect:
        case SyntaxKind::DescendingRangeSelect:
            return RangeSelectExpression::fromSyntax(compilation, value,
                                                     selector->as<RangeSelectSyntax>(), fullRange,
                                                     context);
        default:
            SLANG_UNREACHABLE;
    }
}

static const SyntaxNode* findOverrideNodeSource(const HierarchyOverrideNode& node) {
    // Try to find some concrete syntax node (defparam or bind directive) that
    // caused us to have this override node.
    if (!node.paramOverrides.empty()) {
        for (auto& [_, val] : node.paramOverrides) {
            if (val.second)
                return val.second;
        }
    }

    for (auto& [info, _] : node.binds) {
        if (info.bindSyntax)
            return info.bindSyntax;
    }

    for (auto& [_, val] : node.childNodes) {
        if (auto result = findOverrideNodeSource(val))
            return result;
    }

    return nullptr;
}

Expression* Expression::tryBindInterfaceRef(const ASTContext& context,
                                            const ExpressionSyntax& syntax, bool isInterfacePort) {
    // Unwrap the expression; parentheses are superfluous.
    const ExpressionSyntax* expr = &syntax;
    while (expr->kind == SyntaxKind::ParenthesizedExpression)
        expr = expr->as<ParenthesizedExpressionSyntax>().expression;

    // Connection must be a name (not some arbitrary expression).
    if (!NameSyntax::isKind(expr->kind)) {
        if (isInterfacePort)
            context.addDiag(diag::InterfacePortInvalidExpression, expr->sourceRange());
        return nullptr;
    }

    // Try to look up that name.
    LookupResult result;
    auto flags = isInterfacePort ? LookupFlags::IfacePortConn : LookupFlags::None;
    Lookup::name(expr->as<NameSyntax>(), context, flags, result);

    DeferredSourceRange modportRange;
    std::string_view arrayModportName;
    if (!result.found) {
        // We didn't find the name as-is. This might be a case where the user has
        // provided an explicit modport name on top of an array of interfaces,
        // which we should support by looking up the name again without the trailing
        // name component and taking the result if it's an iface array.
        if (expr->kind == SyntaxKind::ScopedName) {
            auto& scoped = expr->as<ScopedNameSyntax>();
            if (scoped.separator.kind == TokenKind::Dot &&
                scoped.right->kind == SyntaxKind::IdentifierName) {
                LookupResult result2;
                Lookup::name(*scoped.left, context, LookupFlags::None, result2);
                arrayModportName = scoped.right->as<IdentifierNameSyntax>().identifier.valueText();

                auto found = result2.found;
                if (found && !arrayModportName.empty() &&
                    (found->kind == SymbolKind::InterfacePort ||
                     found->kind == SymbolKind::InstanceArray)) {
                    result = result2;
                    modportRange = *scoped.right;
                }
            }
        }

        // If still not found we can't make a connection. Error if this is for a
        // port, and otherwise return null to let the caller try binding as a
        // normal expression.
        if (!result.found) {
            if (isInterfacePort)
                result.reportDiags(context);
            return nullptr;
        }
    }

    auto& comp = context.getCompilation();
    auto symbol = result.found;
    const InterfacePortSymbol* ifacePort = nullptr;
    const ModportSymbol* modport = nullptr;

    // If we found an interface port we should unwrap to what it's connected to.
    if (symbol->kind == SymbolKind::InterfacePort) {
        ifacePort = &symbol->as<InterfacePortSymbol>();
        std::tie(symbol, modport) = ifacePort->getConnection();

        if (symbol && !result.selectors.empty()) {
            SmallVector<const ElementSelectSyntax*> selectors;
            for (auto& sel : result.selectors)
                selectors.push_back(std::get<0>(sel));

            symbol = Lookup::selectChild(*symbol, selectors, context, result);
            result.selectors.clear();
        }

        if (!symbol) {
            // Returning nullptr from this function means to try doing normal expression
            // creation, but if we hit this case here we found the iface and simply failed
            // to connect it, likely because we're in an uninstantiated context. Return
            // a badExpr here to silence any follow on errors that might otherwise result.
            result.reportDiags(context);
            return &badExpr(comp, nullptr);
        }
    }

    // Unwrap any interface arrays we found, collect the dimensions along the way.
    SmallVector<ConstantRange, 4> dims;
    auto origSymbol = symbol;
    while (symbol->kind == SymbolKind::InstanceArray) {
        auto& array = symbol->as<InstanceArraySymbol>();
        if (array.elements.empty())
            return &badExpr(comp, nullptr);

        dims.push_back(array.range);
        symbol = array.elements[0];
    }

    // If we didn't find a modport or an interface instance then this is not
    // an interface connection.
    if (symbol->kind != SymbolKind::Modport &&
        (symbol->kind != SymbolKind::Instance || !symbol->as<InstanceSymbol>().isInterface())) {
        // If this is a variable with an errored type, an error is already emitted.
        if (symbol->kind == SymbolKind::UninstantiatedDef ||
            (symbol->kind == SymbolKind::Variable &&
             symbol->as<VariableSymbol>().getType().isError())) {
            return comp.emplace<ArbitrarySymbolExpression>(*context.scope, *origSymbol,
                                                           comp.getErrorType(), nullptr,
                                                           syntax.sourceRange());
        }

        if (isInterfacePort && !origSymbol->name.empty()) {
            auto& diag = context.addDiag(diag::NotAnInterface, syntax.sourceRange())
                         << origSymbol->name;
            diag.addNote(diag::NoteDeclarationHere, origSymbol->location);
        }

        // Return nullptr to let the parent try normal expression binding.
        return nullptr;
    }

    // At this point we've found a connection so we're no longer speculatively
    // trying to connect, we're going to connect or issue an error.
    result.reportDiags(context);
    result.errorIfSelectors(context);

    auto sourceRange = syntax.sourceRange();
    const InstanceBodySymbol* iface = nullptr;
    if (symbol->kind == SymbolKind::Modport) {
        modport = &symbol->as<ModportSymbol>();
        iface = &symbol->getParentScope()->asSymbol().as<InstanceBodySymbol>();
    }
    else {
        iface = &symbol->as<InstanceSymbol>().body;
    }

    if (!isInterfacePort) {
        if (iface->hierarchyOverrideNode) {
            auto& diag = context.addDiag(diag::VirtualIfaceDefparam, sourceRange);
            if (auto source = findOverrideNodeSource(*iface->hierarchyOverrideNode))
                diag.addNote(diag::NoteDeclarationHere, source->sourceRange());
        }

        if (iface->parentInstance && iface->parentInstance->resolvedConfig) {
            auto& diag = context.addDiag(diag::VirtualIfaceConfigRule, sourceRange);

            auto rc = iface->parentInstance->resolvedConfig;
            if (rc->configRule)
                diag.addNote(diag::NoteConfigRule, rc->configRule->syntax->sourceRange());
            else
                diag.addNote(diag::NoteConfigRule, rc->useConfig.location);
        }
    }

    if (!arrayModportName.empty()) {
        if (modport) {
            // If we connected via an interface port that itself has a modport restriction,
            // we can't also be restricting via an interface array modport.
            auto& diag = context.addDiag(diag::InvalidModportAccess, *modportRange);
            diag << arrayModportName;
            diag << iface->getDefinition().name;
            diag << modport->name;
            return &badExpr(comp, nullptr);
        }
        else {
            auto sym = iface->find(arrayModportName);
            if (!sym || sym->kind != SymbolKind::Modport) {
                auto& diag = context.addDiag(diag::NotAModport, *modportRange);
                diag << arrayModportName;
                diag << iface->getDefinition().name;
                return &badExpr(comp, nullptr);
            }

            modport = &sym->as<ModportSymbol>();
        }
    }

    // Now make sure the interface or modport we found matches the target type.
    // Fabricate a virtual interface type for the rhs that we can use for matching.
    SLANG_ASSERT(iface->parentInstance);
    const Type* type = comp.emplace<VirtualInterfaceType>(*iface->parentInstance, modport,
                                                          /* isRealIface */ true,
                                                          sourceRange.start());
    if (!dims.empty())
        type = &FixedSizeUnpackedArrayType::fromDims(*context.scope, *type, dims, sourceRange);

    // Don't return a modport as the symbol target, it's expected that it
    // will be pulled from the virtual interface type instead.
    if (origSymbol->kind == SymbolKind::Modport) {
        origSymbol = &origSymbol->getParentScope()->asSymbol();
        origSymbol = origSymbol->as<InstanceBodySymbol>().parentInstance;
    }

    auto hierRef = HierarchicalReference::fromLookup(comp, result);
    return comp.emplace<ArbitrarySymbolExpression>(*context.scope, *origSymbol, *type, &hierRef,
                                                   sourceRange);
}

void Expression::findPotentiallyImplicitNets(
    const SyntaxNode& expr, const ASTContext& context,
    SmallVectorBase<const IdentifierNameSyntax*>& results) {

    struct Visitor : public SyntaxVisitor<Visitor> {
        Visitor(const ASTContext& context, SmallVectorBase<const IdentifierNameSyntax*>& results) :
            context(context), results(results) {}

        void handle(const NameSyntax& nameSyntax) {
            if (nameSyntax.kind != SyntaxKind::IdentifierName)
                return;

            bitmask<LookupFlags> flags = LookupFlags::NoUndeclaredError;
            if (context.flags.has(ASTFlags::BindInstantiation))
                flags |= LookupFlags::DisallowWildcardImport | LookupFlags::DisallowUnitReferences;

            LookupResult result;
            ASTContext ctx(*context.scope, LookupLocation::max);
            Lookup::name(nameSyntax, ctx, flags, result);

            SLANG_ASSERT(!result.flags.has(LookupResultFlags::IsHierarchical));

            if (!result.found && !result.hasError())
                results.push_back(&nameSyntax.as<IdentifierNameSyntax>());
        }

        const ASTContext& context;
        SmallVectorBase<const IdentifierNameSyntax*>& results;
    };

    Visitor visitor(context, results);
    expr.visit(visitor);
}

void Expression::contextDetermined(const ASTContext& context, Expression*& expr,
                                   const Expression* parentExpr, const Type& newType,
                                   SourceRange opRange, ConversionKind conversionKind) {
    PropagationVisitor visitor(context, newType, parentExpr, opRange, conversionKind);
    expr = &expr->visit(visitor);
}

void Expression::selfDetermined(const ASTContext& context, Expression*& expr) {
    SLANG_ASSERT(expr->type);
    PropagationVisitor visitor(context, *expr->type, nullptr, {}, ConversionKind::Propagated);
    expr = &expr->visit(visitor);
}

Expression& Expression::selfDetermined(Compilation& compilation, const ExpressionSyntax& syntax,
                                       const ASTContext& context, bitmask<ASTFlags> extraFlags) {
    Expression* expr = &create(compilation, syntax, context, extraFlags);
    selfDetermined(context, expr);
    return *expr;
}

Expression& Expression::badExpr(Compilation& compilation, const Expression* expr) {
    return *compilation.emplace<InvalidExpression>(expr, compilation.getErrorType());
}

Expression::EffectiveSign Expression::conjunction(EffectiveSign left, EffectiveSign right) {
    if (left == EffectiveSign::Either)
        return right;
    if (right == EffectiveSign::Either)
        return left;
    if (left == EffectiveSign::Signed && right == EffectiveSign::Signed)
        return EffectiveSign::Signed;
    return EffectiveSign::Unsigned;
}

bool Expression::signMatches(EffectiveSign left, EffectiveSign right) {
    if (left == EffectiveSign::Either || right == EffectiveSign::Either)
        return true;
    return left == right;
}

void InvalidExpression::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

} // namespace slang::ast
