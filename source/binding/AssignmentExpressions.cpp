//------------------------------------------------------------------------------
// AssignmentExpressions.cpp
// Definitions for assignment-related expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/AssignmentExpressions.h"

#include "slang/binding/LiteralExpressions.h"
#include "slang/binding/MiscExpressions.h"
#include "slang/binding/OperatorExpressions.h"
#include "slang/binding/SelectExpressions.h"
#include "slang/binding/TimingControl.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/NumericDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/AllTypes.h"
#include "slang/symbols/InstanceSymbols.h"
#include "slang/syntax/AllSyntax.h"

namespace {

using namespace slang;

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
        case ExpressionKind::MinTypMax: {
            auto& mtm = expr.as<MinTypMaxExpression>();
            return recurseCheckEnum(mtm.selected());
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

Expression& Expression::implicitConversion(const BindContext& context, const Type& targetType,
                                           Expression& expr) {
    ASSERT(targetType.isAssignmentCompatible(*expr.type) ||
           ((targetType.isString() || targetType.isByteArray()) && expr.isImplicitString()) ||
           (targetType.isEnum() && isSameEnum(expr, targetType)));

    Expression* result = &expr;
    selfDetermined(context, result);
    return *context.scope.getCompilation().emplace<ConversionExpression>(targetType, true, *result,
                                                                         result->sourceRange);
}

Expression* Expression::tryConnectPortArray(const BindContext& context, const Type& portType,
                                            Expression& expr, const InstanceSymbol& instance) {
    // This lambda is shared code for reporting an error and returning an invalid expression.
    auto& comp = context.getCompilation();
    auto bad = [&]() {
        auto& diag = context.addDiag(diag::PortConnArrayMismatch, expr.sourceRange);
        diag << *expr.type << portType;

        string_view name = instance.getArrayName();
        if (name.empty())
            diag << "<unknown>"sv;
        else {
            diag << name;
            if (instance.location)
                diag << SourceRange{ instance.location, instance.location + name.length() };
        }

        return &badExpr(comp, &expr);
    };

    // Collect all of the dimensions of the instance array that owns the provided instance, ex:
    // MyMod instArray [3][4] (.conn(vec));
    //                 ^~~~~~  // these guys
    SmallVectorSized<ConstantRange, 8> instanceDimVec;
    instance.getArrayDimensions(instanceDimVec);

    span<const ConstantRange> instanceDims = instanceDimVec;
    span<const int32_t> arrayPath = instance.arrayPath;

    // If the connection has any unpacked dimensions, match them up with
    // the leading instance dimensions now.
    Expression* result = &expr;
    const Type* ct = &expr.type->getCanonicalType();
    if (ct->kind == SymbolKind::FixedSizeUnpackedArrayType) {
        SmallVectorSized<ConstantRange, 8> unpackedDimVec;
        const FixedSizeUnpackedArrayType* curr = &ct->as<FixedSizeUnpackedArrayType>();
        while (true) {
            unpackedDimVec.append(curr->range);
            ct = &curr->elementType.getCanonicalType();
            if (ct->kind != SymbolKind::FixedSizeUnpackedArrayType)
                break;

            curr = &ct->as<FixedSizeUnpackedArrayType>();
        }

        // Select each element of the connection array based on the index of
        // the instance in the instance array path. Elements get matched
        // left index to left index.
        span<const ConstantRange> unpackedDims = unpackedDimVec;
        size_t common = std::min(instanceDims.size(), unpackedDims.size());
        for (size_t i = 0; i < common; i++) {
            if (unpackedDims[i].width() != instanceDims[i].width())
                return bad();

            // To select the right element, translate the path index since it's
            // relative to that particular array's declared range.
            int32_t index = instanceDims[i].translateIndex(arrayPath[i]);

            // Now translate back to be relative to the connection type's declared range.
            if (!unpackedDims[i].isLittleEndian())
                index = unpackedDims[i].upper() - index;
            else
                index = unpackedDims[i].lower() + index;

            result = &ElementSelectExpression::fromConstant(comp, *result, index, context);
            if (result->bad())
                return result; // probably unreachable
        }

        unpackedDims = unpackedDims.subspan(common);
        instanceDims = instanceDims.subspan(common);
        arrayPath = arrayPath.subspan(common);

        // If there are still unpacked dims left, we will have consumed
        // all of the instance dims and whatever is left should match
        // the actual port type to connect.
        if (!unpackedDims.empty()) {
            if (!portType.isEquivalent(
                    FixedSizeUnpackedArrayType::fromDims(comp, *ct, unpackedDims))) {
                return bad();
            }

            ASSERT(instanceDims.empty());
            ASSERT(arrayPath.empty());
            return result;
        }

        // If there are no instance dims left, just make sure the remaining type matches
        // the port and we're good to go.
        if (instanceDims.empty())
            return portType.isEquivalent(*ct) ? result : bad();

        // Otherwise, if there are instance dimemsions left there needs to be packed dimensions
        // in the connection to match up with them.
        if (ct->kind != SymbolKind::PackedArrayType)
            return bad();
    }
    else if (ct->kind != SymbolKind::PackedArrayType) {
        return nullptr;
    }

    // If we reach this point we're looking at a packed array connection; if there were
    // any unpacked dimensions we already stripped them off and accounted for them.
    // The port type must be integral since we're assigning a packed array.
    if (!portType.isIntegral())
        return bad();

    // The width of the port times the number of instances must match the number of bits
    // we have remaining in the connection.
    bitwidth_t numInstances = 1;
    for (auto& dim : instanceDims)
        numInstances *= dim.width();

    bitwidth_t portWidth = portType.getBitWidth();
    if (numInstances * portWidth != ct->getBitWidth())
        return bad();

    // Convert the port expression to a simple bit vector so that we can select
    // bit ranges from it -- the range select expression works on the declared
    // range of the packed array so a multidimensional wouldn't work correctly
    // without this conversion.
    result = &implicitConversion(context, comp.getType(portWidth, result->type->getIntegralFlags()),
                                 *result);

    // We have enough bits to assign each port on each instance, so now we just need
    // to pick the right ones. The spec says we start with all right hand indices
    // to match the rightmost part select, iterating through the rightmost dimension first.
    // We know none of these operations will overflow because we already checked that
    // the full size matches the incoming connection above.
    int32_t offset = 0;
    for (size_t i = 0; i < arrayPath.size(); i++) {
        if (i > 0)
            offset *= int32_t(instanceDims[i - 1].width());
        offset += instanceDims[i].translateIndex(arrayPath[i]);
    }

    int32_t width = int32_t(portWidth);
    offset *= width;
    ConstantRange range{ offset + width - 1, offset };
    return &RangeSelectExpression::fromConstant(comp, *result, range, context);
}

bool Expression::isImplicitlyAssignableTo(const Type& targetType) const {
    return targetType.isAssignmentCompatible(*type) ||
           (targetType.isString() && isImplicitString()) ||
           (targetType.isEnum() && isSameEnum(*this, *type));
}

Expression& Expression::convertAssignment(const BindContext& context, const Type& type,
                                          Expression& expr, SourceLocation location,
                                          optional<SourceRange> lhsRange) {
    if (expr.bad())
        return expr;

    Compilation& compilation = context.scope.getCompilation();
    if (type.isError())
        return badExpr(compilation, &expr);

    Expression* result = &expr;
    const Type* rt = expr.type;
    if (type.isEquivalent(*rt)) {
        selfDetermined(context, result);
        return *result;
    }

    // If this is a port connection to an array of instances, check if the provided
    // expression represents an array that should be sliced on a per-instance basis.
    if (context.instance && !context.instance->arrayPath.empty()) {
        Expression* conn = tryConnectPortArray(context, type, expr, *context.instance);
        if (conn) {
            selfDetermined(context, conn);
            return *conn;
        }
    }

    if (!type.isAssignmentCompatible(*rt)) {
        // String literals have a type of integer, but are allowed to implicitly convert to the
        // string type. See comments on isSameEnum for why that's here as well.
        if (((type.isString() || type.isByteArray()) && expr.isImplicitString()) ||
            (type.isEnum() && isSameEnum(expr, type))) {

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

    if (type.isNumeric() && rt->isNumeric()) {
        if ((context.flags & BindFlags::EnumInitializer) != 0 &&
            !checkEnumInitializer(context, type, *result)) {

            return badExpr(compilation, &expr);
        }

        rt = binaryOperatorType(compilation, &type, rt, false);
        contextDetermined(context, result, *rt);

        if (type.isEquivalent(*rt)) {
            result->type = &type;
            return *result;
        }

        result =
            compilation.emplace<ConversionExpression>(type, true, *result, result->sourceRange);
    }
    else {
        result = &implicitConversion(context, type, *result);
    }

    selfDetermined(context, result);

    // If this is an enum initializer and we just discarded unknown bits by
    // implicitly converting to a 2-state result, the standard says we
    // should declare this an error.
    if ((context.flags & BindFlags::EnumInitializer) != 0 && !type.isFourState()) {
        ConstantValue cv = context.tryEval(expr);
        if (cv.isInteger() && cv.integer().hasUnknown()) {
            context.addDiag(diag::EnumValueUnknownBits, expr.sourceRange) << cv << type;
            return badExpr(compilation, result);
        }
    }

    return *result;
}

Expression& AssignmentExpression::fromSyntax(Compilation& compilation,
                                             const BinaryExpressionSyntax& syntax,
                                             const BindContext& context) {
    if ((context.flags & BindFlags::AssignmentAllowed) == 0) {
        if (context.flags & BindFlags::ProceduralStatement)
            context.addDiag(diag::AssignmentRequiresParens, syntax.sourceRange());
        else
            context.addDiag(diag::AssignmentNotAllowed, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    optional<BinaryOperator> op;
    if (syntax.kind != SyntaxKind::AssignmentExpression &&
        syntax.kind != SyntaxKind::NonblockingAssignmentExpression) {
        op = getBinaryOperator(syntax.kind);
    }

    const ExpressionSyntax* rightExpr = syntax.right;
    bool isNonBlocking = syntax.kind == SyntaxKind::NonblockingAssignmentExpression;

    // If we're in a procedural statement, check for an intra-assignment timing control.
    // Otherwise, we'll let this fall through to the default handler which will issue an error.
    const TimingControl* timingControl = nullptr;
    if ((context.flags & BindFlags::ProceduralStatement) &&
        rightExpr->kind == SyntaxKind::TimingControlExpression) {

        auto& tce = rightExpr->as<TimingControlExpressionSyntax>();
        timingControl = &TimingControl::bind(*tce.timing, context);
        rightExpr = tce.expr;
    }

    // The right hand side of an assignment expression is typically an
    // "assignment-like context", except if the left hand side does not
    // have a self-determined type. That can only be true if the lhs is
    // an assignment pattern without an explicit type.
    if (syntax.left->kind == SyntaxKind::AssignmentPatternExpression) {
        auto& pattern = syntax.left->as<AssignmentPatternExpressionSyntax>();
        if (!pattern.type) {
            // In this case we have to bind the rhs first to determine the
            // correct type to use as the context for the lhs.
            Expression* rhs = &selfDetermined(compilation, *rightExpr, context);
            if (rhs->bad())
                return badExpr(compilation, rhs);

            Expression* lhs =
                &create(compilation, *syntax.left, context, BindFlags::None, rhs->type);
            selfDetermined(context, lhs);

            return fromComponents(compilation, op, isNonBlocking, *lhs, *rhs,
                                  syntax.operatorToken.location(), timingControl,
                                  syntax.sourceRange(), context);
        }
    }

    Expression& lhs = selfDetermined(compilation, *syntax.left, context);
    Expression& rhs = create(compilation, *rightExpr, context, BindFlags::None, lhs.type);

    return fromComponents(compilation, op, isNonBlocking, lhs, rhs, syntax.operatorToken.location(),
                          timingControl, syntax.sourceRange(), context);
}

Expression& AssignmentExpression::fromComponents(
    Compilation& compilation, optional<BinaryOperator> op, bool nonBlocking, Expression& lhs,
    Expression& rhs, SourceLocation assignLoc, const TimingControl* timingControl,
    SourceRange sourceRange, const BindContext& context) {

    auto result = compilation.emplace<AssignmentExpression>(op, nonBlocking, *lhs.type, lhs, rhs,
                                                            timingControl, sourceRange);
    if (lhs.bad() || rhs.bad())
        return badExpr(compilation, result);

    // Make sure we can actually assign to the thing on the lhs.
    if (!lhs.verifyAssignable(context, nonBlocking, assignLoc))
        return badExpr(compilation, result);

    result->right_ =
        &convertAssignment(context, *lhs.type, *result->right_, assignLoc, lhs.sourceRange);
    if (result->right_->bad())
        return badExpr(compilation, result);

    return *result;
}

ConstantValue AssignmentExpression::evalImpl(EvalContext& context) const {
    if (!context.isScriptEval() && timingControl)
        return nullptr;

    LValue lvalue = left().evalLValue(context);
    ConstantValue rvalue = right().eval(context);
    if (!lvalue || !rvalue)
        return nullptr;

    if (isCompound())
        rvalue = evalBinaryOperator(*op, lvalue.load(), rvalue);

    lvalue.store(rvalue);
    return rvalue;
}

bool AssignmentExpression::verifyConstantImpl(EvalContext& context) const {
    if (!context.isScriptEval() && timingControl) {
        context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
        return false;
    }

    return left().verifyConstant(context) && right().verifyConstant(context);
}

void AssignmentExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("left", left());
    serializer.write("right", right());
    serializer.write("isNonBlocking", isNonBlocking());
    if (op)
        serializer.write("op", toString(*op));
    if (timingControl)
        serializer.write("timingControl", *timingControl);
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

    // SignedCastExpression can also represent a const cast, which does nothing
    // and passes the type through unchanged.
    if (syntax.signing.kind == TokenKind::ConstKeyword) {
        result->type = operand.type;
        return *result;
    }

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

ConstantValue ConversionExpression::evalImpl(EvalContext& context) const {
    if (!isImplicit && !type->isCastCompatible(*operand().type, false)) {
        // bit-stream casting
        auto value = operand().eval(context);
        if (value == nullptr)
            return value;
        auto v1 = type->bitstreamCast(value);
        if (v1 == nullptr) {
            auto& diag = context.addDiag(diag::ConstEvalBitstreamCastSize, sourceRange);
            diag << value.bitstreamWidth() << *type;
        }
        return v1;
    }
    return convert(context, *operand().type, *type, sourceRange, operand().eval(context));
}

ConstantValue ConversionExpression::convert(EvalContext& context, const Type& from, const Type& to,
                                            SourceRange sourceRange, ConstantValue&& value) {
    if (!value)
        return nullptr;

    if (from.isMatching(to))
        return std::move(value);

    if (to.isIntegral())
        return value.convertToInt(to.getBitWidth(), to.isSigned(), to.isFourState());

    if (to.isFloating()) {
        switch (to.getBitWidth()) {
            case 32:
                return value.convertToShortReal();
            case 64:
                return value.convertToReal();
            default:
                THROW_UNREACHABLE;
        }
    }

    if (to.isString())
        return value.convertToStr();

    if (to.isUnpackedArray() && from.isUnpackedArray()) {
        // Conversion to a dynamic array just resizes. Conversion to a fixed array
        // must have the same number of elements in the source.
        ASSERT(!to.hasFixedRange() || !from.hasFixedRange());
        if (to.hasFixedRange()) {
            size_t size = value.size();
            if (size != to.getFixedRange().width()) {
                context.addDiag(diag::ConstEvalDynamicToFixedSize, sourceRange)
                    << from << size << to;
                return nullptr;
            }
        }

        if (!to.isQueue() && from.isQueue()) {
            // Convert from queue to vector.
            auto& q = *value.queue();
            return std::vector(q.begin(), q.end());
        }

        if (to.isQueue() && !from.isQueue()) {
            // Convert from vector to queue.
            auto elems = value.elements();
            return SVQueue(elems.begin(), elems.end());
        }

        return std::move(value);
    }

    if (to.isByteArray()) {
        const auto& ct = to.getCanonicalType();
        const auto isSigned = ct.getArrayElementType()->isSigned();
        if (ct.isQueue()) {
            return value.convertToByteQueue(isSigned);
        }
        else {
            bitwidth_t size;
            if (ct.hasFixedRange())
                size = ct.as<FixedSizeUnpackedArrayType>().range.width();
            else
                size = 0; // dynamic array use string size
            return value.convertToByteArray(size, isSigned);
        }
    }

    // TODO: other types
    THROW_UNREACHABLE;
}

bool ConversionExpression::verifyConstantImpl(EvalContext& context) const {
    return operand().verifyConstant(context);
}

void ConversionExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("operand", operand());
}

Expression& NewArrayExpression::fromSyntax(Compilation& compilation,
                                           const NewArrayExpressionSyntax& syntax,
                                           const BindContext& context,
                                           const Type* assignmentTarget) {
    if (!assignmentTarget ||
        assignmentTarget->getCanonicalType().kind != SymbolKind::DynamicArrayType) {
        context.addDiag(diag::NewArrayTarget, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    auto& sizeExpr = selfDetermined(compilation, *syntax.sizeExpr, context);
    const Expression* initExpr = nullptr;
    if (syntax.initializer) {
        initExpr = &bindRValue(*assignmentTarget, *syntax.initializer->expression,
                               syntax.initializer->getFirstToken().location(), context);
    }

    auto result = compilation.emplace<NewArrayExpression>(*assignmentTarget, sizeExpr, initExpr,
                                                          syntax.sourceRange());
    if (sizeExpr.bad() || (initExpr && initExpr->bad()))
        return badExpr(compilation, result);

    if (!sizeExpr.type->isIntegral()) {
        context.addDiag(diag::ExprMustBeIntegral, sizeExpr.sourceRange);
        return badExpr(compilation, result);
    }

    return *result;
}

ConstantValue NewArrayExpression::evalImpl(EvalContext& context) const {
    ConstantValue sz = sizeExpr().eval(context);
    if (!sz)
        return nullptr;

    optional<int64_t> size = sz.integer().as<int64_t>();
    if (!size || *size < 0) {
        context.addDiag(diag::InvalidArraySize, sizeExpr().sourceRange) << sz;
        return nullptr;
    }

    size_t count = size_t(*size);
    size_t index = 0;
    std::vector<ConstantValue> result(count);

    ConstantValue iv;
    if (initExpr()) {
        iv = initExpr()->eval(context);
        if (!iv)
            return nullptr;

        auto elems = iv.elements();
        for (; index < count && index < elems.size(); index++)
            result[index] = elems[index];
    }

    // Any remaining elements are default initialized.
    ConstantValue def = type->getArrayElementType()->getDefaultValue();
    for (; index < count; index++)
        result[index] = def;

    return result;
}

bool NewArrayExpression::verifyConstantImpl(EvalContext& context) const {
    return sizeExpr().verifyConstant(context) &&
           (!initExpr() || initExpr()->verifyConstant(context));
}

void NewArrayExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("sizeExpr", sizeExpr());
    if (initExpr())
        serializer.write("initExpr", initExpr());
}

} // namespace slang
