//------------------------------------------------------------------------------
// AssignmentExpressions.cpp
// Definitions for assignment-related expressions
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/expressions/AssignmentExpressions.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/Bitstream.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/expressions/CallExpression.h"
#include "slang/ast/expressions/ConversionExpression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/symbols/ClassSymbols.h"
#include "slang/ast/symbols/CoverSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/diagnostics/TypesDiags.h"
#include "slang/numeric/MathUtils.h"
#include "slang/syntax/AllSyntax.h"

namespace slang::ast {

using namespace parsing;
using namespace syntax;

Expression* Expression::tryConnectPortArray(const ASTContext& context, const Type& portType,
                                            Expression& expr, const InstanceSymbolBase& instance) {
    // This lambda is shared code for reporting an error and returning an invalid expression.
    auto& comp = context.getCompilation();
    auto bad = [&]() {
        auto& diag = context.addDiag(diag::PortConnArrayMismatch, expr.sourceRange);
        diag << *expr.type << portType;

        std::string_view name = instance.getArrayName();
        if (name.empty())
            diag << "<unknown>"sv;
        else {
            diag << name;
            if (instance.location)
                diag << SourceRange{instance.location, instance.location + name.length()};
        }

        return &badExpr(comp, &expr);
    };

    // Collect all of the dimensions of the instance array that owns the provided instance, ex:
    // MyMod instArray [3][4] (.conn(vec));
    //                 ^~~~~~  // these guys
    SmallVector<ConstantRange> instanceDimVec;
    instance.getArrayDimensions(instanceDimVec);

    std::span<const ConstantRange> instanceDims = instanceDimVec;
    std::span<const int32_t> arrayPath = instance.arrayPath;

    // If the connection has any unpacked dimensions, match them up with
    // the leading instance dimensions now.
    Expression* result = &expr;
    const Type* ct = &expr.type->getCanonicalType();
    if (ct->kind == SymbolKind::FixedSizeUnpackedArrayType) {
        SmallVector<ConstantRange> unpackedDimVec;
        const FixedSizeUnpackedArrayType* curr = &ct->as<FixedSizeUnpackedArrayType>();
        while (true) {
            unpackedDimVec.push_back(curr->range);
            ct = &curr->elementType.getCanonicalType();
            if (ct->kind != SymbolKind::FixedSizeUnpackedArrayType)
                break;

            curr = &ct->as<FixedSizeUnpackedArrayType>();
        }

        // Select each element of the connection array based on the index of
        // the instance in the instance array path. Elements get matched
        // left index to left index.
        std::span<const ConstantRange> unpackedDims = unpackedDimVec;
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
            auto& unpackedType = FixedSizeUnpackedArrayType::fromDims(*context.scope, *ct,
                                                                      unpackedDims,
                                                                      expr.sourceRange);
            if (!portType.isEquivalent(unpackedType)) {
                return bad();
            }

            SLANG_ASSERT(instanceDims.empty());
            SLANG_ASSERT(arrayPath.empty());
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
    auto instPortWidth = checkedMulU32(numInstances, portWidth);
    if (!instPortWidth || *instPortWidth != ct->getBitWidth())
        return bad();

    // Convert the port expression to a simple bit vector so that we can select
    // bit ranges from it -- the range select expression works on the declared
    // range of the packed array so a multidimensional wouldn't work correctly
    // without this conversion.
    //
    // We set the UnevaluatedBranch flag here so that we don't get any warnings
    // related to implicit conversions.
    auto& vecType = comp.getType(*instPortWidth, result->type->getIntegralFlags());
    result = &ConversionExpression::makeImplicit(context.resetFlags(ASTFlags::UnevaluatedBranch),
                                                 vecType, ConversionKind::Implicit, *result,
                                                 nullptr, {});

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
    ConstantRange range{offset + width - 1, offset};
    return &RangeSelectExpression::fromConstant(comp, *result, range, context);
}

Expression& AssignmentExpression::fromSyntax(Compilation& compilation,
                                             const BinaryExpressionSyntax& syntax,
                                             const ASTContext& context) {
    bitmask<AssignFlags> assignFlags;
    bool isNonBlocking = syntax.kind == SyntaxKind::NonblockingAssignmentExpression;
    if (isNonBlocking)
        assignFlags = AssignFlags::NonBlocking;

    if (isNonBlocking && context.flags.has(ASTFlags::Final)) {
        context.addDiag(diag::NonblockingInFinal, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    if (!context.flags.has(ASTFlags::AssignmentAllowed)) {
        if (!context.flags.has(ASTFlags::NonProcedural) &&
            !context.flags.has(ASTFlags::AssignmentDisallowed)) {
            context.addDiag(diag::AssignmentRequiresParens, syntax.sourceRange());
        }
        else {
            context.addDiag(diag::AssignmentNotAllowed, syntax.sourceRange());
        }
        return badExpr(compilation, nullptr);
    }

    bitmask<ASTFlags> extraFlags = ASTFlags::None;
    std::optional<BinaryOperator> op;
    if (syntax.kind != SyntaxKind::AssignmentExpression &&
        syntax.kind != SyntaxKind::NonblockingAssignmentExpression) {
        op = OpInfo::getBinary(syntax.kind);
    }
    else {
        extraFlags |= ASTFlags::StreamingAllowed;
    }

    const ExpressionSyntax* rightExpr = syntax.right;

    // If we're in a top-level statement, check for an intra-assignment timing control.
    // Otherwise, we'll let this fall through to the default handler which will issue an error.
    const TimingControl* timingControl = nullptr;
    if (context.flags.has(ASTFlags::TopLevelStatement) &&
        rightExpr->kind == SyntaxKind::TimingControlExpression) {

        ASTContext timingCtx = context;
        timingCtx.flags |= ASTFlags::LValue;
        if (isNonBlocking)
            timingCtx.flags |= ASTFlags::NonBlockingTimingControl;

        auto& tce = rightExpr->as<TimingControlExpressionSyntax>();
        timingControl = &TimingControl::bind(*tce.timing, timingCtx);
        rightExpr = tce.expr;
    }

    // The right hand side of an assignment expression is typically an
    // "assignment-like context", except if the left hand side does not
    // have a self-determined type. That can only be true if the lhs is
    // an assignment pattern without an explicit type.
    // However, streaming concatenation has no explicit type either so it is excluded and such right
    // hand side will lead to diag::AssignmentPatternNoContext error later.
    if (syntax.left->kind == SyntaxKind::AssignmentPatternExpression &&
        rightExpr->kind != SyntaxKind::StreamingConcatenationExpression) {
        auto& pattern = syntax.left->as<AssignmentPatternExpressionSyntax>();
        if (!pattern.type) {
            // In this case we have to bind the rhs first to determine the
            // correct type to use as the context for the lhs.
            auto rhs = &selfDetermined(compilation, *rightExpr, context);
            auto lhs = &create(compilation, *syntax.left, context, ASTFlags::LValue, rhs->type);
            selfDetermined(context, lhs);

            return fromComponents(compilation, op, assignFlags, *lhs, *rhs,
                                  syntax.operatorToken.range(), timingControl, syntax.sourceRange(),
                                  context);
        }
    }

    auto& lhs = selfDetermined(compilation, *syntax.left, context, extraFlags | ASTFlags::LValue);

    Expression* rhs = nullptr;
    if (lhs.type->isVirtualInterfaceOrArray())
        rhs = tryBindInterfaceRef(context, *rightExpr, /* isInterfacePort */ false);

    if (!rhs) {
        // When LHS is a streaming concatenation which has no explicit type, RHS should be
        // self-determined and we cannot pass lsh.type to it. When both LHS and RHS are streaming
        // concatenations, pass lhs.type to notify RHS to exclude associative arrays for
        // isBitstreamType check, while RHS can still be self-determined by ignoring lhs type
        // information.
        if (lhs.kind == ExpressionKind::Streaming &&
            rightExpr->kind != SyntaxKind::StreamingConcatenationExpression) {
            rhs = &selfDetermined(compilation, *rightExpr, context, extraFlags);
        }
        else {
            rhs = &create(compilation, *rightExpr, context, extraFlags, lhs.type);
        }
    }

    return fromComponents(compilation, op, assignFlags, lhs, *rhs, syntax.operatorToken.range(),
                          timingControl, syntax.sourceRange(), context);
}

Expression& AssignmentExpression::fromComponents(
    Compilation& compilation, std::optional<BinaryOperator> op, bitmask<AssignFlags> flags,
    Expression& lhs, Expression& rhs, SourceRange opRange, const TimingControl* timingControl,
    SourceRange sourceRange, const ASTContext& context) {

    auto result = compilation.emplace<AssignmentExpression>(op, flags.has(AssignFlags::NonBlocking),
                                                            *lhs.type, lhs, rhs, timingControl,
                                                            sourceRange);

    if (lhs.bad() || rhs.bad())
        return badExpr(compilation, result);

    if (lhs.kind == ExpressionKind::Streaming) {
        if (!Bitstream::canBeTarget(lhs.as<StreamingConcatenationExpression>(), rhs, opRange,
                                    context)) {
            return badExpr(compilation, result);
        }

        if (!lhs.requireLValue(context, opRange.start(), flags))
            return badExpr(compilation, result);

        return *result;
    }

    // If this is a compound assignment operator create a binary expression that will
    // apply the operator for us on the right hand side.
    if (op) {
        auto lvalRef = compilation.emplace<LValueReferenceExpression>(*lhs.type, lhs.sourceRange);
        result->right_ = &BinaryExpression::fromComponents(*lvalRef, *result->right_, *op, opRange,
                                                           sourceRange, context);
    }

    result->right_ = &convertAssignment(context, *lhs.type, *result->right_, opRange,
                                        &result->left_, &flags);
    if (result->right_->bad())
        return badExpr(compilation, result);

    if (!result->left_->requireLValue(context, opRange.start(), flags))
        return badExpr(compilation, result);

    if (timingControl) {
        // Cycle delays are only allowed on clock vars, and clock vars
        // cannot use any timing control other than cycle delays.
        if (auto sym = lhs.getSymbolReference(); sym && sym->kind == SymbolKind::ClockVar) {
            if (timingControl->kind != TimingControlKind::CycleDelay) {
                SLANG_ASSERT(timingControl->syntax);
                context.addDiag(diag::ClockVarBadTiming, timingControl->syntax->sourceRange());
            }
        }
        else if (timingControl->kind == TimingControlKind::CycleDelay) {
            SLANG_ASSERT(timingControl->syntax);
            context.addDiag(diag::CycleDelayNonClock, timingControl->syntax->sourceRange());
        }
    }

    return *result;
}

bool AssignmentExpression::isLValueArg() const {
    return right().kind == ExpressionKind::EmptyArgument ||
           (right().kind == ExpressionKind::Conversion &&
            right().as<ConversionExpression>().operand().kind == ExpressionKind::EmptyArgument);
}

ConstantValue AssignmentExpression::evalImpl(EvalContext& context) const {
    if (!context.flags.has(EvalFlags::IsScript) && timingControl) {
        context.addDiag(diag::ConstEvalTimedStmtNotConst, sourceRange);
        return nullptr;
    }

    if (left().kind == ExpressionKind::Streaming) {
        return Bitstream::evaluateTarget(left().as<StreamingConcatenationExpression>(), right(),
                                         context);
    }

    LValue lvalue = left().evalLValue(context);
    if (!lvalue)
        return nullptr;

    if (isCompound())
        context.pushLValue(lvalue);

    ConstantValue rvalue = right().eval(context);

    if (isCompound())
        context.popLValue();

    if (!rvalue)
        return nullptr;

    // If the LHS is an assignment pattern we need to manually apply any conversions
    // to the elements of the RHS since there's no other place to do it.
    if (left().kind == ExpressionKind::SimpleAssignmentPattern)
        rvalue = left().as<SimpleAssignmentPatternExpression>().applyConversions(context, rvalue);

    lvalue.store(rvalue);
    return rvalue;
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

Expression& NewArrayExpression::fromSyntax(Compilation& compilation,
                                           const NewArrayExpressionSyntax& syntax,
                                           const ASTContext& context,
                                           const Type* assignmentTarget) {
    if (!assignmentTarget ||
        assignmentTarget->getCanonicalType().kind != SymbolKind::DynamicArrayType) {

        if (!assignmentTarget || !assignmentTarget->isError())
            context.addDiag(diag::NewArrayTarget, syntax.sourceRange());

        if (!assignmentTarget)
            assignmentTarget = &compilation.getErrorType();
    }

    auto& sizeExpr = selfDetermined(compilation, *syntax.sizeExpr, context);
    const Expression* initExpr = nullptr;
    if (syntax.initializer)
        initExpr = &bindRValue(*assignmentTarget, *syntax.initializer->expression, {}, context);

    auto result = compilation.emplace<NewArrayExpression>(*assignmentTarget, sizeExpr, initExpr,
                                                          syntax.sourceRange());
    if (sizeExpr.bad() || (initExpr && initExpr->bad()))
        return badExpr(compilation, result);

    if (!context.requireIntegral(sizeExpr))
        return badExpr(compilation, result);

    return *result;
}

ConstantValue NewArrayExpression::evalImpl(EvalContext& context) const {
    ConstantValue sz = sizeExpr().eval(context);
    if (!sz)
        return nullptr;

    std::optional<int64_t> size = sz.integer().as<int64_t>();
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

void NewArrayExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("sizeExpr", sizeExpr());
    if (initExpr())
        serializer.write("initExpr", *initExpr());
}

static std::pair<const ClassType*, bool> resolveNewClassTarget(const NameSyntax& nameSyntax,
                                                               const ASTContext& context,
                                                               const Type*& assignmentTarget,
                                                               SourceRange range) {
    // If the new expression is typed, look up that type as the target.
    // Otherwise, the target must come from the expression context.
    bool isSuperClass = false;
    const ClassType* classType = nullptr;
    if (nameSyntax.kind == SyntaxKind::ConstructorName) {
        if (!assignmentTarget || !assignmentTarget->isClass()) {
            if (!assignmentTarget || !assignmentTarget->isError())
                context.addDiag(diag::NewClassTarget, range);
            return {nullptr, false};
        }

        classType = &assignmentTarget->getCanonicalType().as<ClassType>();
    }
    else {
        auto& scoped = nameSyntax.as<ScopedNameSyntax>();
        if (scoped.left->getLastToken().kind == TokenKind::SuperKeyword) {
            // This is a super.new invocation, so find the base class's
            // constructor. This is relative to our current context, not
            // any particular assignment target.
            auto [ct, _] = Lookup::getContainingClass(*context.scope);
            classType = ct;
            if (!classType || classType->name.empty()) {
                // Parser already emitted an error for this case.
                return {nullptr, false};
            }

            auto base = classType->getBaseClass();
            if (!base) {
                context.addDiag(diag::SuperNoBase, nameSyntax.sourceRange()) << classType->name;
                return {nullptr, false};
            }

            if (base->isError())
                return {nullptr, false};

            classType = &base->as<Type>().getCanonicalType().as<ClassType>();
            assignmentTarget = &context.getCompilation().getVoidType();
            isSuperClass = true;
        }
        else {
            auto& className = *nameSyntax.as<ScopedNameSyntax>().left;
            classType = Lookup::findClass(className, context);
            if (!classType)
                return {nullptr, false};

            assignmentTarget = classType;
        }
    }

    if (!isSuperClass && classType->isAbstract) {
        context.addDiag(diag::NewVirtualClass, range) << classType->name;
        return {nullptr, false};
    }

    if (!isSuperClass && classType->isInterface) {
        context.addDiag(diag::NewInterfaceClass, range) << classType->name;
        return {nullptr, false};
    }

    return {classType, isSuperClass};
}

Expression& NewClassExpression::fromSyntax(Compilation& comp,
                                           const NewClassExpressionSyntax& syntax,
                                           const ASTContext& context,
                                           const Type* assignmentTarget) {
    // The new keyword can also be used to create covergroups.
    if (syntax.scopedNew->kind == SyntaxKind::ConstructorName && assignmentTarget &&
        assignmentTarget->isCovergroup()) {
        return NewCovergroupExpression::fromSyntax(comp, syntax, context, *assignmentTarget);
    }

    SourceRange range = syntax.sourceRange();
    auto [classType, isSuperClass] = resolveNewClassTarget(*syntax.scopedNew, context,
                                                           assignmentTarget, range);
    if (!classType)
        return badExpr(comp, nullptr);

    Expression* constructorCall = nullptr;
    if (auto constructor = classType->getConstructor()) {
        Lookup::ensureVisible(*constructor, context, range);
        constructorCall = &CallExpression::fromArgs(comp, &constructor->as<SubroutineSymbol>(),
                                                    nullptr, syntax.argList, range, context);
    }
    else if (syntax.argList && !syntax.argList->parameters.empty()) {
        auto& diag = context.addDiag(diag::TooManyArguments, syntax.argList->sourceRange());
        diag << "new"sv;
        diag << 0;
        diag << syntax.argList->parameters.size();
    }

    return *comp.emplace<NewClassExpression>(*assignmentTarget, constructorCall, isSuperClass,
                                             range);
}

Expression& NewClassExpression::fromSyntax(Compilation& comp,
                                           const SuperNewDefaultedArgsExpressionSyntax& syntax,
                                           const ASTContext& context,
                                           const Type* assignmentTarget) {
    SourceRange range = syntax.sourceRange();
    auto [classType, isSuperClass] = resolveNewClassTarget(*syntax.scopedNew, context,
                                                           assignmentTarget, range);
    if (!classType)
        return badExpr(comp, nullptr);

    SLANG_ASSERT(isSuperClass);

    // The containing constructor (should be our parent scope)
    // must have a 'default' argument as well.
    if (context.scope->asSymbol().kind == SymbolKind::Subroutine) {
        auto& sub = context.scope->asSymbol().as<SubroutineSymbol>();
        if (!sub.flags.has(MethodFlags::DefaultedSuperArg))
            context.addDiag(diag::InvalidSuperNewDefault, range);
    }

    return *comp.emplace<NewClassExpression>(*assignmentTarget, nullptr, isSuperClass, range);
}

ConstantValue NewClassExpression::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalClassType, sourceRange);
    return nullptr;
}

void NewClassExpression::serializeTo(ASTSerializer& serializer) const {
    if (constructorCall())
        serializer.write("constructorCall", *constructorCall());
    serializer.write("isSuperClass", isSuperClass);
}

Expression& NewCovergroupExpression::fromSyntax(Compilation& compilation,
                                                const NewClassExpressionSyntax& syntax,
                                                const ASTContext& context,
                                                const Type& assignmentTarget) {
    auto range = syntax.sourceRange();
    auto& coverType = assignmentTarget.getCanonicalType().as<CovergroupType>();

    SmallVector<const Expression*> args;
    if (!CallExpression::bindArgs(syntax.argList, coverType.getArguments(), "new"sv, range, context,
                                  args, /* isBuiltInMethod */ false)) {
        return badExpr(compilation, nullptr);
    }

    return *compilation.emplace<NewCovergroupExpression>(assignmentTarget, args.copy(compilation),
                                                         range);
}

ConstantValue NewCovergroupExpression::evalImpl(EvalContext& context) const {
    context.addDiag(diag::ConstEvalCovergroupType, sourceRange);
    return nullptr;
}

void NewCovergroupExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("arguments");
    for (auto arg : arguments)
        serializer.serialize(*arg);
    serializer.endArray();
}

Expression& Expression::bindAssignmentPattern(Compilation& comp,
                                              const AssignmentPatternExpressionSyntax& syntax,
                                              const ASTContext& context,
                                              const Type* assignmentTarget) {
    SourceRange range = syntax.sourceRange();

    if (syntax.type) {
        assignmentTarget = &comp.getType(*syntax.type, context);
        if (!assignmentTarget->isSimpleType() && syntax.type->kind != SyntaxKind::TypeReference) {
            if (!assignmentTarget->isError())
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
    if (ct.kind == SymbolKind::PackedStructType) {
        structScope = &ct.as<PackedStructType>();
    }
    else if (ct.kind == SymbolKind::UnpackedStructType) {
        structScope = &ct.as<UnpackedStructType>();
    }
    else if (ct.kind == SymbolKind::PackedArrayType) {
        auto& ua = ct.as<PackedArrayType>();
        elementType = &ua.elementType;
        numElements = ua.range.width();
    }
    else if (ct.kind == SymbolKind::FixedSizeUnpackedArrayType) {
        auto& ua = ct.as<FixedSizeUnpackedArrayType>();
        elementType = &ua.elementType;
        numElements = ua.range.width();
    }
    else if (ct.kind == SymbolKind::DynamicArrayType ||
             ct.kind == SymbolKind::AssociativeArrayType || ct.kind == SymbolKind::QueueType) {
        elementType = ct.getArrayElementType();
    }
    else if (ct.isIntegral() && ct.kind != SymbolKind::ScalarType) {
        elementType = ct.isFourState() ? &comp.getLogicType() : &comp.getBitType();
        numElements = ct.getBitWidth();
    }
    else {
        context.addDiag(diag::BadAssignmentPatternType, range) << type;
        return badExpr(comp, nullptr);
    }

    const AssignmentPatternSyntax& p = *syntax.pattern;
    if (context.flags.has(ASTFlags::LValue) && p.kind != SyntaxKind::SimpleAssignmentPattern) {
        context.addDiag(diag::ExpressionNotAssignable, range);
        return badExpr(comp, nullptr);
    }

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
                SLANG_UNREACHABLE;
        }
    }
    else if (ct.kind == SymbolKind::DynamicArrayType || ct.kind == SymbolKind::QueueType) {
        switch (p.kind) {
            case SyntaxKind::SimpleAssignmentPattern:
                return SimpleAssignmentPatternExpression::forDynamicArray(
                    comp, p.as<SimpleAssignmentPatternSyntax>(), context, type, *elementType,
                    range);
            case SyntaxKind::StructuredAssignmentPattern:
                return StructuredAssignmentPatternExpression::forDynamicArray(
                    comp, p.as<StructuredAssignmentPatternSyntax>(), context, type, *elementType,
                    range);
            case SyntaxKind::ReplicatedAssignmentPattern:
                return ReplicatedAssignmentPatternExpression::forDynamicArray(
                    comp, p.as<ReplicatedAssignmentPatternSyntax>(), context, type, *elementType,
                    range);
            default:
                SLANG_UNREACHABLE;
        }
    }
    else if (ct.kind == SymbolKind::AssociativeArrayType) {
        switch (p.kind) {
            case SyntaxKind::SimpleAssignmentPattern:
            case SyntaxKind::ReplicatedAssignmentPattern:
                context.addDiag(diag::AssignmentPatternAssociativeType, range);
                return badExpr(comp, nullptr);
            case SyntaxKind::StructuredAssignmentPattern:
                return StructuredAssignmentPatternExpression::forAssociativeArray(
                    comp, p.as<StructuredAssignmentPatternSyntax>(), context, type, *elementType,
                    range);
            default:
                SLANG_UNREACHABLE;
        }
    }
    else {
        switch (p.kind) {
            case SyntaxKind::SimpleAssignmentPattern:
                return SimpleAssignmentPatternExpression::forFixedArray(
                    comp, p.as<SimpleAssignmentPatternSyntax>(), context, type, *elementType,
                    numElements, range);
            case SyntaxKind::StructuredAssignmentPattern:
                return StructuredAssignmentPatternExpression::forFixedArray(
                    comp, p.as<StructuredAssignmentPatternSyntax>(), context, type, *elementType,
                    range);
            case SyntaxKind::ReplicatedAssignmentPattern:
                return ReplicatedAssignmentPatternExpression::forFixedArray(
                    comp, p.as<ReplicatedAssignmentPatternSyntax>(), context, type, *elementType,
                    numElements, range);
            default:
                SLANG_UNREACHABLE;
        }
    }
}

ConstantValue AssignmentPatternExpressionBase::evalImpl(EvalContext& context) const {
    size_t replCount = 1;
    if (kind == ExpressionKind::ReplicatedAssignmentPattern) {
        auto countVal = as<ReplicatedAssignmentPatternExpression>()
                            .count()
                            .eval(context)
                            .integer()
                            .as<int32_t>();
        SLANG_ASSERT(countVal >= 0);
        replCount = size_t(*countVal);
    }

    if (type->isIntegral()) {
        SmallVector<SVInt> values;
        for (size_t i = 0; i < replCount; i++) {
            for (auto elem : elements()) {
                ConstantValue v = elem->eval(context);
                if (!v)
                    return nullptr;

                values.push_back(v.integer());
            }
        }

        return SVInt::concat(values);
    }
    else if (type->isAssociativeArray()) {
        // Special casing for associative arrays: there is no contiguous set of
        // elements, so downcast to the known type (must be a Structured pattern)
        // and build the map from the index setters.
        AssociativeArray values;
        auto& sap = as<StructuredAssignmentPatternExpression>();
        for (auto& setter : sap.indexSetters) {
            SLANG_ASSERT(setter.expr && setter.index);
            ConstantValue key = setter.index->eval(context);
            ConstantValue val = setter.expr->eval(context);
            if (!key || !val)
                return nullptr;

            values.try_emplace(std::move(key), std::move(val));
        }

        if (sap.defaultSetter) {
            values.defaultValue = sap.defaultSetter->eval(context);
            if (!values.defaultValue)
                return nullptr;
        }

        return values;
    }
    else if (type->isQueue()) {
        SVQueue result;
        result.maxBound = type->getCanonicalType().as<QueueType>().maxBound;
        for (size_t i = 0; i < replCount; i++) {
            for (auto elem : elements()) {
                result.emplace_back(elem->eval(context));
                if (result.back().bad())
                    return nullptr;
            }
        }

        result.resizeToBound();
        return result;
    }
    else {
        std::vector<ConstantValue> values;
        for (size_t i = 0; i < replCount; i++) {
            for (auto elem : elements()) {
                values.emplace_back(elem->eval(context));
                if (values.back().bad())
                    return nullptr;
            }
        }

        return values;
    }
}

void AssignmentPatternExpressionBase::serializeTo(ASTSerializer& serializer) const {
    if (!elements().empty()) {
        serializer.startArray("elements");
        for (auto elem : elements())
            serializer.serialize(*elem);
        serializer.endArray();
    }
}

Expression& SimpleAssignmentPatternExpression::forStruct(
    Compilation& comp, const SimpleAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Scope& structScope, SourceRange sourceRange) {

    SmallVector<const Type*> types;
    for (auto& field : structScope.membersOfType<FieldSymbol>())
        types.push_back(&field.getType());

    if (types.size() != syntax.items.size()) {
        auto& diag = context.addDiag(diag::WrongNumberAssignmentPatterns, sourceRange);
        diag << type << types.size() << syntax.items.size();
        return badExpr(comp, nullptr);
    }

    const bool isLValue = context.flags.has(ASTFlags::LValue);
    auto direction = isLValue ? ArgumentDirection::Out : ArgumentDirection::In;

    bool bad = false;
    uint32_t index = 0;
    SmallVector<const Expression*> elems;
    for (auto item : syntax.items) {
        auto& expr = Expression::bindArgument(*types[index++], direction, {}, *item, context);
        elems.push_back(&expr);
        bad |= expr.bad();
    }

    auto result = comp.emplace<SimpleAssignmentPatternExpression>(type, isLValue, elems.copy(comp),
                                                                  sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

static std::span<const Expression* const> bindExpressionList(
    const Type& patternType, const Type& elementType, size_t replCount, bitwidth_t expectedCount,
    const SeparatedSyntaxList<ExpressionSyntax>& items, const ASTContext& context,
    SourceRange sourceRange, bool& bad) {

    const bool isLValue = context.flags.has(ASTFlags::LValue);
    auto direction = isLValue ? ArgumentDirection::Out : ArgumentDirection::In;

    SmallVector<const Expression*> elems;
    for (auto item : items) {
        auto& expr = Expression::bindArgument(elementType, direction, {}, *item, context);
        elems.push_back(&expr);
        bad |= expr.bad();
    }

    if (!bad && expectedCount && expectedCount != elems.size() * replCount) {
        auto& diag = context.addDiag(diag::WrongNumberAssignmentPatterns, sourceRange);
        diag << patternType << expectedCount << elems.size();
        bad = true;
    }

    return elems.copy(context.getCompilation());
}

Expression& SimpleAssignmentPatternExpression::forFixedArray(
    Compilation& comp, const SimpleAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, bitwidth_t numElements, SourceRange sourceRange) {

    bool bad = false;
    auto elems = bindExpressionList(type, elementType, 1, numElements, syntax.items, context,
                                    sourceRange, bad);

    const bool isLValue = context.flags.has(ASTFlags::LValue);
    auto result = comp.emplace<SimpleAssignmentPatternExpression>(type, isLValue, elems,
                                                                  sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& SimpleAssignmentPatternExpression::forDynamicArray(
    Compilation& comp, const SimpleAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    const bool isLValue = context.flags.has(ASTFlags::LValue);
    if (isLValue) {
        context.addDiag(diag::AssignmentPatternLValueDynamic, sourceRange);
        return badExpr(comp, nullptr);
    }

    bool bad = false;
    auto elems = bindExpressionList(type, elementType, 1, 0, syntax.items, context, sourceRange,
                                    bad);

    auto result = comp.emplace<SimpleAssignmentPatternExpression>(type, isLValue, elems,
                                                                  sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

LValue SimpleAssignmentPatternExpression::evalLValueImpl(EvalContext& context) const {
    std::vector<LValue> lvals;
    lvals.reserve(elements().size());
    for (auto elem : elements()) {
        LValue lval = elem->as<AssignmentExpression>().left().evalLValue(context);
        if (!lval)
            return nullptr;

        lvals.emplace_back(std::move(lval));
    }

    auto lvalKind = type->isIntegral() ? LValue::Concat::Packed : LValue::Concat::Unpacked;
    return LValue(std::move(lvals), lvalKind);
}

ConstantValue SimpleAssignmentPatternExpression::applyConversions(EvalContext& context,
                                                                  const ConstantValue& rval) const {
    if (rval.isInteger()) {
        auto& ri = rval.integer();
        int32_t msb = int32_t(ri.getBitWidth()) - 1;

        SmallVector<SVInt> ints;
        for (auto elem : elements()) {
            auto& elemRhs = elem->as<AssignmentExpression>().right();
            if (elemRhs.kind == ExpressionKind::Conversion) {
                auto& conv = elemRhs.as<ConversionExpression>();
                if (conv.isImplicit()) {
                    auto width = int32_t(conv.operand().type->getBitWidth());
                    ints.emplace_back(
                        conv.applyTo(context, ri.slice(msb, msb - width + 1)).integer());
                    msb -= width;
                    continue;
                }
            }

            auto width = int32_t(elemRhs.type->getBitWidth());
            ints.emplace_back(ri.slice(msb, msb - width + 1));
            msb -= width;
        }

        return SVInt::concat(ints);
    }
    else {
        auto rvalElems = rval.elements();
        SLANG_ASSERT(rvalElems.size() == elements().size());

        size_t i = 0;
        std::vector<ConstantValue> newElems;
        for (auto elem : elements()) {
            auto& elemRhs = elem->as<AssignmentExpression>().right();
            auto currVal = rvalElems[i++];
            if (elemRhs.kind == ExpressionKind::Conversion) {
                auto& conv = elemRhs.as<ConversionExpression>();
                if (conv.isImplicit()) {
                    newElems.emplace_back(conv.applyTo(context, std::move(currVal)));
                    continue;
                }
            }

            newElems.emplace_back(std::move(currVal));
        }

        return newElems;
    }
}

static const Expression* matchElementValue(
    const ASTContext& context, const Type& elementType, const FieldSymbol* targetField,
    SourceRange sourceRange,
    std::span<const StructuredAssignmentPatternExpression::TypeSetter> typeSetters,
    const Expression* defaultSetter) {

    // Every element in the array or structure must be covered by one of:
    // index:value      -- recorded in the indexMap (handled only at the top level, not here)
    // member:value     -- recorded in the memberMap (handled only at the top level, not here)
    // type:value       -- recorded in typeSetters, last one takes precedence
    // default:value    -- recorded in defaultSetter, types must be assignable
    // struct element   -- recursively descend into the struct
    // array element    -- recursively descend into the array

    if (elementType.isError())
        return nullptr;

    // Try all type setters for a match. Last one that matches wins.
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
    const ExpressionSyntax* defaultSyntax = nullptr;
    if (defaultSetter) {
        defaultSyntax = defaultSetter->syntax;
        SLANG_ASSERT(defaultSyntax);
    }

    if (defaultSetter) {
        if (elementType.isMatching(*defaultSetter->type))
            return defaultSetter;

        if (elementType.isSimpleBitVector() &&
            elementType.isAssignmentCompatible(*defaultSetter->type)) {
            return &Expression::bindRValue(elementType, *defaultSyntax, {}, context);
        }
    }

    // Otherwise, we check first if the type is a struct or array, in which
    // case we descend recursively into its members before continuing on with the default.
    if (elementType.isStruct()) {
        const Scope* structScope;
        if (elementType.isUnpackedStruct())
            structScope = &elementType.getCanonicalType().as<UnpackedStructType>();
        else
            structScope = &elementType.getCanonicalType().as<PackedStructType>();

        SmallVector<const Expression*> elements;
        for (auto& field : structScope->membersOfType<FieldSymbol>()) {
            const Type& type = field.getType();
            if (type.isError() || field.name.empty())
                return nullptr;

            auto elemExpr = matchElementValue(context, type, &field, sourceRange, typeSetters,
                                              defaultSetter);
            if (!elemExpr)
                return nullptr;

            elements.push_back(elemExpr);
        }

        auto& comp = context.getCompilation();
        return comp.emplace<SimpleAssignmentPatternExpression>(elementType, /* isLValue */ false,
                                                               elements.copy(comp), sourceRange);
    }

    if (elementType.isArray() && elementType.hasFixedRange()) {
        auto nestedElemType = elementType.getArrayElementType();
        SLANG_ASSERT(nestedElemType);

        auto elemExpr = matchElementValue(context, *nestedElemType, nullptr, sourceRange,
                                          typeSetters, defaultSetter);
        if (!elemExpr)
            return nullptr;

        SmallVector<const Expression*> elements;
        auto arrayRange = elementType.getFixedRange();
        for (int32_t i = arrayRange.lower(); i <= arrayRange.upper(); i++)
            elements.push_back(elemExpr);

        auto& comp = context.getCompilation();
        return comp.emplace<SimpleAssignmentPatternExpression>(elementType, /* isLValue */ false,
                                                               elements.copy(comp), sourceRange);
    }

    // Finally, if we have a default then it must now be assignment compatible.
    if (defaultSetter)
        return &Expression::bindRValue(elementType, *defaultSyntax, {}, context);

    // Otherwise there's no setter for this element, which is an error.
    if (targetField) {
        auto& diag = context.addDiag(diag::AssignmentPatternNoMember, sourceRange);
        diag << targetField->name;
        diag.addNote(diag::NoteDeclarationHere, targetField->location);
    }
    else {
        context.addDiag(diag::AssignmentPatternMissingElements, sourceRange);
    }

    return nullptr;
}

Expression& StructuredAssignmentPatternExpression::forStruct(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Scope& structScope, SourceRange sourceRange) {

    bool bad = false;
    const Expression* defaultSetter = nullptr;
    SmallMap<const Symbol*, const Expression*, 8> memberMap;
    SmallVector<MemberSetter, 4> memberSetters;
    SmallVector<TypeSetter, 4> typeSetters;

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
                auto& expr = bindRValue(member->as<FieldSymbol>().getType(), *item->expr,
                                        nameToken.range(), context);
                bad |= expr.bad();

                auto [it, inserted] = memberMap.emplace(member, &expr);
                if (!inserted) {
                    auto& diag = context.addDiag(diag::AssignmentPatternKeyDupName,
                                                 item->key->sourceRange());
                    diag << name;
                    diag.addNote(diag::NotePreviousDefinition, it->second->sourceRange);
                    bad = true;
                    continue;
                }

                memberSetters.emplace_back(MemberSetter{member, &expr});
            }
            else {
                auto found = Lookup::unqualified(*context.scope, name, LookupFlags::Type);
                if (found && found->isType()) {
                    auto& expr = bindRValue(found->as<Type>(), *item->expr, nameToken.range(),
                                            context);
                    bad |= expr.bad();

                    typeSetters.emplace_back(TypeSetter{&found->as<Type>(), &expr});
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
            const Type& typeKey = comp.getType(item->key->as<DataTypeSyntax>(), context);
            if (typeKey.isSimpleType()) {
                auto& expr = bindRValue(typeKey, *item->expr, {}, context);
                typeSetters.emplace_back(TypeSetter{&typeKey, &expr});
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

    SmallVector<const Expression*> elements;
    for (auto& field : structScope.membersOfType<FieldSymbol>()) {
        // If we already have a setter for this field we don't have to do anything else.
        if (auto it = memberMap.find(&field); it != memberMap.end()) {
            elements.push_back(it->second);
            continue;
        }

        const Type& fieldType = field.getType();
        if (fieldType.isError() || field.name.empty()) {
            bad = true;
            continue;
        }

        auto expr = matchElementValue(context, fieldType, &field, sourceRange, typeSetters,
                                      defaultSetter);
        if (!expr) {
            bad = true;
            continue;
        }

        elements.push_back(expr);
    }

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, memberSetters.copy(comp), typeSetters.copy(comp), std::span<const IndexSetter>{},
        defaultSetter, elements.copy(comp), sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

static std::optional<int32_t> bindArrayIndexSetter(
    const ASTContext& context, const Expression& keyExpr, const Type& elementType,
    const ExpressionSyntax& valueSyntax, SmallMap<int32_t, const Expression*, 8>& indexMap,
    SmallVectorBase<StructuredAssignmentPatternExpression::IndexSetter>& indexSetters) {

    std::optional<int32_t> index = context.evalInteger(keyExpr);
    if (!index)
        return std::nullopt;

    auto& expr = Expression::bindRValue(elementType, valueSyntax, {}, context);
    if (expr.bad())
        return std::nullopt;

    auto [it, inserted] = indexMap.emplace(*index, &expr);
    if (!inserted) {
        auto& diag = context.addDiag(diag::AssignmentPatternKeyDupValue, keyExpr.sourceRange);
        diag << *index;
        diag.addNote(diag::NotePreviousDefinition, it->second->sourceRange);
        return std::nullopt;
    }

    indexSetters.push_back({&keyExpr, &expr});
    return index;
}

Expression& StructuredAssignmentPatternExpression::forFixedArray(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    bool bad = false;
    const Expression* defaultSetter = nullptr;
    SmallMap<int32_t, const Expression*, 8> indexMap;
    SmallVector<IndexSetter, 4> indexSetters;
    SmallVector<TypeSetter, 4> typeSetters;

    for (auto item : syntax.items) {
        if (item->key->kind == SyntaxKind::DefaultPatternKeyExpression) {
            if (defaultSetter) {
                context.addDiag(diag::AssignmentPatternKeyDupDefault, item->key->sourceRange());
                bad = true;
            }
            defaultSetter = &selfDetermined(comp, *item->expr, context);
            bad |= defaultSetter->bad();
            continue;
        }

        // The key is either an array index or a data type setter.
        auto& keyExpr = Expression::bind(*item->key, context, ASTFlags::AllowDataType);
        if (keyExpr.bad()) {
            bad = true;
            continue;
        }

        if (keyExpr.kind == ExpressionKind::DataType) {
            const Type& typeKey = *keyExpr.type;
            if (typeKey.isSimpleType()) {
                auto& expr = bindRValue(typeKey, *item->expr, {}, context);
                typeSetters.emplace_back(TypeSetter{&typeKey, &expr});
                bad |= expr.bad();
            }
            else {
                context.addDiag(diag::AssignmentPatternKeyExpr, item->key->sourceRange());
                bad = true;
            }
        }
        else {
            auto index = bindArrayIndexSetter(context, keyExpr, elementType, *item->expr, indexMap,
                                              indexSetters);
            if (!index) {
                bad = true;
                continue;
            }

            if (!type.getFixedRange().containsPoint(*index)) {
                auto& diag = context.addDiag(diag::IndexValueInvalid, keyExpr.sourceRange);
                diag << *index;
                diag << type;
                bad = true;
            }
        }
    }

    SmallVector<const Expression*> elements;
    std::optional<const Expression*> cachedVal;
    auto arrayRange = type.getFixedRange();

    for (int32_t i = arrayRange.lower(); i <= arrayRange.upper(); i++) {
        // If we already have a setter for this index we don't have to do anything else.
        if (auto it = indexMap.find(i); it != indexMap.end()) {
            elements.push_back(it->second);
            continue;
        }

        if (!cachedVal) {
            cachedVal = matchElementValue(context, elementType, nullptr, syntax.sourceRange(),
                                          typeSetters, defaultSetter);
            if (!cachedVal.value()) {
                bad = true;
                break;
            }
        }

        elements.push_back(*cachedVal);
    }

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, std::span<const MemberSetter>{}, typeSetters.copy(comp), indexSetters.copy(comp),
        defaultSetter, elements.copy(comp), sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& StructuredAssignmentPatternExpression::forDynamicArray(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    bool bad = false;
    SmallMap<int32_t, const Expression*, 8> indexMap;
    SmallVector<IndexSetter, 4> indexSetters;
    size_t maxIndex = 0;

    for (auto item : syntax.items) {
        if (item->key->kind == SyntaxKind::DefaultPatternKeyExpression) {
            context.addDiag(diag::AssignmentPatternDynamicDefault, item->key->sourceRange());
            bad = true;
            continue;
        }

        // The key is either an array index or a data type setter.
        auto& keyExpr = Expression::bind(*item->key, context, ASTFlags::AllowDataType);
        if (keyExpr.bad()) {
            bad = true;
            continue;
        }

        if (keyExpr.kind == ExpressionKind::DataType) {
            context.addDiag(diag::AssignmentPatternDynamicType, item->key->sourceRange());
            bad = true;
            continue;
        }

        auto index = bindArrayIndexSetter(context, keyExpr, elementType, *item->expr, indexMap,
                                          indexSetters);
        if (!context.requirePositive(index, keyExpr.sourceRange)) {
            bad = true;
            continue;
        }

        maxIndex = std::max(maxIndex, size_t(*index));
    }

    SmallVector<const Expression*> elements;
    if (indexMap.size() != maxIndex + 1) {
        if (!bad) {
            context.addDiag(diag::AssignmentPatternMissingElements, sourceRange);
            bad = true;
        }
    }
    else {
        elements.reserve(maxIndex + 1);
        for (size_t i = 0; i <= maxIndex; i++) {
            auto expr = indexMap[int32_t(i)];
            SLANG_ASSERT(expr);
            elements.push_back(expr);
        }
    }

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, std::span<const MemberSetter>{}, std::span<const TypeSetter>{},
        indexSetters.copy(comp), nullptr, elements.copy(comp), sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& StructuredAssignmentPatternExpression::forAssociativeArray(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    bool bad = false;
    const Expression* defaultSetter = nullptr;
    SmallVector<IndexSetter, 4> indexSetters;
    SmallMap<ConstantValue, SourceRange, 8> indexMap;

    const Type* indexType = type.getAssociativeIndexType();

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
            context.addDiag(diag::AssignmentPatternDynamicType, item->key->sourceRange());
            bad = true;
        }
        else {
            const Expression* indexExpr;
            if (indexType)
                indexExpr = &bindRValue(*indexType, *item->key, {}, context);
            else
                indexExpr = &Expression::bind(*item->key, context);

            if (!indexExpr->bad()) {
                auto cv = context.eval(*indexExpr);
                if (!cv)
                    bad = true;
                else {
                    auto [it, inserted] = indexMap.emplace(cv, indexExpr->sourceRange);
                    if (!inserted) {
                        auto& diag = context.addDiag(diag::AssignmentPatternKeyDupValue,
                                                     indexExpr->sourceRange);
                        diag << cv;
                        diag.addNote(diag::NotePreviousDefinition, it->second);
                        bad = true;
                    }
                }
            }

            auto& expr = bindRValue(elementType, *item->expr, {}, context);
            bad |= expr.bad() || indexExpr->bad();

            indexSetters.push_back(IndexSetter{indexExpr, &expr});
        }
    }

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, std::span<const MemberSetter>{}, std::span<const TypeSetter>{},
        indexSetters.copy(comp), defaultSetter, std::span<const Expression*>{}, sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

void StructuredAssignmentPatternExpression::serializeTo(ASTSerializer& serializer) const {
    if (defaultSetter)
        serializer.write("defaultSetter", *defaultSetter);

    if (!memberSetters.empty()) {
        serializer.startArray("memberSetters");
        for (auto& setter : memberSetters) {
            serializer.startObject();
            serializer.writeLink("member", *setter.member);
            serializer.write("expr", *setter.expr);
            serializer.endObject();
        }
        serializer.endArray();
    }

    if (!typeSetters.empty()) {
        serializer.startArray("typeSetters");
        for (auto& setter : typeSetters) {
            serializer.startObject();
            serializer.write("type", *setter.type);
            serializer.write("expr", *setter.expr);
            serializer.endObject();
        }
        serializer.endArray();
    }

    if (!indexSetters.empty()) {
        serializer.startArray("indexSetters");
        for (auto& setter : indexSetters) {
            serializer.startObject();
            serializer.write("index", *setter.index);
            serializer.write("expr", *setter.expr);
            serializer.endObject();
        }
        serializer.endArray();
    }
}

const Expression& ReplicatedAssignmentPatternExpression::bindReplCount(
    Compilation& comp, const ExpressionSyntax& syntax, const ASTContext& context, size_t& count) {

    const Expression& expr = bind(syntax, context);
    std::optional<int32_t> c = context.evalInteger(expr);
    if (!context.requireGtZero(c, expr.sourceRange))
        return badExpr(comp, &expr);

    count = size_t(*c);
    return expr;
}

Expression& ReplicatedAssignmentPatternExpression::forStruct(
    Compilation& comp, const ReplicatedAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Scope& structScope, SourceRange sourceRange) {

    size_t count = 0;
    auto& countExpr = bindReplCount(comp, *syntax.countExpr, context, count);
    if (countExpr.bad())
        return badExpr(comp, nullptr);

    SmallVector<const Type*> types;
    for (auto& field : structScope.membersOfType<FieldSymbol>())
        types.push_back(&field.getType());

    if (types.size() != syntax.items.size() * count) {
        auto& diag = context.addDiag(diag::WrongNumberAssignmentPatterns, sourceRange);
        diag << type << types.size() << syntax.items.size() * count;
        return badExpr(comp, nullptr);
    }

    bool bad = false;
    size_t index = 0;
    SmallVector<const Expression*> elems;
    for (auto item : syntax.items) {
        auto& expr = Expression::bindRValue(*types[index++], *item, {}, context);
        elems.push_back(&expr);
        bad |= expr.bad();
    }

    auto result = comp.emplace<ReplicatedAssignmentPatternExpression>(type, countExpr,
                                                                      elems.copy(comp),
                                                                      sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& ReplicatedAssignmentPatternExpression::forFixedArray(
    Compilation& comp, const ReplicatedAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, bitwidth_t numElements, SourceRange sourceRange) {

    size_t count = 0;
    auto& countExpr = bindReplCount(comp, *syntax.countExpr, context, count);
    if (countExpr.bad())
        return badExpr(comp, nullptr);

    bool bad = false;
    auto elems = bindExpressionList(type, elementType, count, numElements, syntax.items, context,
                                    sourceRange, bad);

    auto result = comp.emplace<ReplicatedAssignmentPatternExpression>(type, countExpr, elems,
                                                                      sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& ReplicatedAssignmentPatternExpression::forDynamicArray(
    Compilation& comp, const ReplicatedAssignmentPatternSyntax& syntax, const ASTContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    size_t count = 0;
    auto& countExpr = bindReplCount(comp, *syntax.countExpr, context, count);
    if (countExpr.bad())
        return badExpr(comp, nullptr);

    bool bad = false;
    auto elems = bindExpressionList(type, elementType, count, 0, syntax.items, context, sourceRange,
                                    bad);

    auto result = comp.emplace<ReplicatedAssignmentPatternExpression>(type, countExpr, elems,
                                                                      sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

void ReplicatedAssignmentPatternExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("count", count());
    AssignmentPatternExpressionBase::serializeTo(serializer);
}

} // namespace slang::ast
