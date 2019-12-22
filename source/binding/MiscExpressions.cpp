//------------------------------------------------------------------------------
// MiscExpressions.cpp
// Definitions for miscellaneous expressions.
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#include "slang/binding/MiscExpressions.h"

#include <nlohmann/json.hpp>

#include "slang/binding/SystemSubroutine.h"
#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/symbols/MemberSymbols.h"
#include "slang/symbols/ParameterSymbols.h"
#include "slang/symbols/Type.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"

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

bool checkArrayIndex(EvalContext& context, const Type& type, const ConstantValue& cs,
                     const std::string& str, SourceRange sourceRange, int32_t& result) {
    optional<int32_t> index = cs.integer().as<int32_t>();
    if (index && type.isString()) {
        if (*index < 0 || size_t(*index) >= str.size()) {
            context.addDiag(diag::NoteStringIndexInvalid, sourceRange) << cs << str.size();
            return false;
        }

        result = *index;
        return true;
    }

    ConstantRange range = type.getArrayRange();
    if (!index || !range.containsPoint(*index)) {
        context.addDiag(diag::NoteArrayIndexInvalid, sourceRange) << cs << type;
        return false;
    }

    result = range.translateIndex(*index);
    return true;
}

} // namespace

namespace slang {

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

ConstantValue NamedValueExpression::evalImpl(EvalContext& context) const {
    if (!verifyConstantImpl(context))
        return nullptr;

    switch (symbol.kind) {
        case SymbolKind::Parameter:
            // Special case for parameters: if this parameter is the child of a
            // definition symbol, the value it has isn't real (because it's not
            // part of a real instance). Just return nullptr here so that we don't
            // end up reporting a spurious error for a definition that is never
            // instantiated. If it does ever get instantiated, we'll catch any real
            // errors in the instance itself.
            if (symbol.getParentScope()->asSymbol().kind == SymbolKind::Definition)
                return nullptr;

            return symbol.as<ParameterSymbol>().getValue();
        case SymbolKind::EnumValue:
            return symbol.as<EnumValueSymbol>().getValue();
        default:
            ConstantValue* v = context.findLocal(&symbol);
            if (v)
                return *v;
            break;
    }

    // If we reach this point, the variable was not found, which should mean that
    // it's not actually constant.
    context.addDiag(diag::NoteNonConstVariable, sourceRange) << symbol.name;
    context.addDiag(diag::NoteDeclarationHere, symbol.location);
    return nullptr;
}

LValue NamedValueExpression::evalLValueImpl(EvalContext& context) const {
    if (!verifyConstantImpl(context))
        return nullptr;

    auto cv = context.findLocal(&symbol);
    if (!cv) {
        context.addDiag(diag::NoteNonConstVariable, sourceRange) << symbol.name;
        context.addDiag(diag::NoteDeclarationHere, symbol.location);
        return nullptr;
    }

    return LValue(*cv);
}

bool NamedValueExpression::verifyConstantImpl(EvalContext& context) const {
    if (context.isScriptEval())
        return true;

    // Hierarchical names are disallowed in constant expressions and constant functions
    if (isHierarchical) {
        context.addDiag(diag::NoteHierarchicalNameInCE, sourceRange) << symbol.name;
        return false;
    }

    const EvalContext::Frame& frame = context.topFrame();
    const SubroutineSymbol* subroutine = frame.subroutine;
    if (!subroutine)
        return true;

    // Constant functions have a bunch of additional restrictions. See [13.4.4]:
    // - All parameter values used within the function shall be defined before the use of
    //   the invoking constant function call.
    // - All identifiers that are not parameters or functions shall be declared locally to
    //   the current function.
    if (symbol.kind != SymbolKind::Parameter && symbol.kind != SymbolKind::EnumValue) {
        const Scope* scope = symbol.getParentScope();
        while (scope && scope != subroutine)
            scope = scope->asSymbol().getParentScope();

        if (scope != subroutine) {
            context.addDiag(diag::NoteFunctionIdentifiersMustBeLocal, sourceRange);
            context.addDiag(diag::NoteDeclarationHere, symbol.location);
            return false;
        }
    }
    else {
        bool isBefore;
        auto frameScope = frame.lookupLocation.getScope();
        if (!frameScope || symbol.getParentScope() == frameScope)
            isBefore = LookupLocation::after(symbol) < frame.lookupLocation;
        else {
            // If the two locations are not in the same compilation unit, assume that it's ok.
            auto compare = symbol.isBeforeInCompilationUnit(frameScope->asSymbol());
            isBefore = compare.value_or(true);
        }

        if (!isBefore) {
            context.addDiag(diag::NoteIdUsedInCEBeforeDecl, sourceRange) << symbol.name;
            context.addDiag(diag::NoteDeclarationHere, symbol.location);
            return false;
        }
    }

    return true;
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

ConstantValue ElementSelectExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    ConstantValue cs = selector().eval(context);
    if (!cv || !cs)
        return nullptr;

    std::string str = value().type->isString() ? cv.str() : "";

    int32_t index;
    if (!checkArrayIndex(context, *value().type, cs, str, sourceRange, index))
        return nullptr;

    if (value().type->isUnpackedArray())
        return cv.elements()[size_t(index)];

    if (value().type->isString())
        return cv.getSlice(index, index);

    // For packed arrays, we're selecting bit ranges, not necessarily single bits.
    int32_t width = (int32_t)type->getBitWidth();
    index *= width;
    return cv.integer().slice(index + width - 1, index);
}

LValue ElementSelectExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    ConstantValue cs = selector().eval(context);
    if (!lval || !cs)
        return nullptr;

    const std::string& str = value().type->isString() ? lval.load().str() : "";

    int32_t index;
    if (!checkArrayIndex(context, *value().type, cs, str, sourceRange, index))
        return nullptr;

    if (value().type->isUnpackedArray())
        return lval.selectIndex(index);

    if (value().type->isString())
        return lval.selectRange({ index, index });

    // For packed arrays, we're selecting bit ranges, not necessarily single bits.
    int32_t width = (int32_t)type->getBitWidth();
    index *= width;
    return lval.selectRange({ index + width - 1, index });
}

bool ElementSelectExpression::verifyConstantImpl(EvalContext& context) const {
    return value().verifyConstant(context) && selector().verifyConstant(context);
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

ConstantValue RangeSelectExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    ConstantValue cl = left().eval(context);
    ConstantValue cr = right().eval(context);
    if (!cv || !cl || !cr)
        return nullptr;

    optional<ConstantRange> range = getRange(context, cl, cr);
    if (!range)
        return nullptr;

    return cv.getSlice(range->upper(), range->lower());
}

LValue RangeSelectExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    ConstantValue cl = left().eval(context);
    ConstantValue cr = right().eval(context);
    if (!lval || !cl || !cr)
        return nullptr;

    optional<ConstantRange> range = getRange(context, cl, cr);
    if (!range)
        return nullptr;

    return lval.selectRange(*range);
}

bool RangeSelectExpression::verifyConstantImpl(EvalContext& context) const {
    return value().verifyConstant(context) && left().verifyConstant(context) &&
           right().verifyConstant(context);
}

optional<ConstantRange> RangeSelectExpression::getRange(EvalContext& context,
                                                        const ConstantValue& cl,
                                                        const ConstantValue& cr) const {
    ConstantRange result;
    const Type& valueType = *value().type;
    ConstantRange valueRange = valueType.getArrayRange();

    if (selectionKind == RangeSelectionKind::Simple) {
        result = type->getArrayRange();
    }
    else {
        optional<int32_t> l = cl.integer().as<int32_t>();
        if (!l) {
            context.addDiag(diag::NoteArrayIndexInvalid, sourceRange) << cl << valueType;
            return std::nullopt;
        }

        optional<int32_t> r = cr.integer().as<int32_t>();
        result = getIndexedRange(selectionKind, *l, *r, valueRange.isLittleEndian());
    }

    if (!valueRange.containsPoint(result.left) || !valueRange.containsPoint(result.right)) {
        auto& diag = context.addDiag(diag::NotePartSelectInvalid, sourceRange);
        diag << result.left << result.right;
        diag << valueType;
        return std::nullopt;
    }

    if (!result.isLittleEndian())
        result.reverse();

    result.left = valueRange.translateIndex(result.left);
    result.right = valueRange.translateIndex(result.right);

    if (!valueType.isPackedArray())
        return result;

    // For packed arrays we're potentially selecting multi-bit elements.
    int32_t width =
        (int32_t)valueType.getCanonicalType().as<PackedArrayType>().elementType.getBitWidth();

    result.left *= width;
    result.right *= width;
    result.left += width - 1;

    return result;
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

ConstantValue MemberAccessExpression::evalImpl(EvalContext& context) const {
    ConstantValue cv = value().eval(context);
    if (!cv)
        return nullptr;

    // TODO: handle unpacked unions
    if (value().type->isUnpackedStruct())
        return cv.elements()[field.offset];

    int32_t offset = (int32_t)field.offset;
    int32_t width = (int32_t)type->getBitWidth();
    return cv.integer().slice(width + offset - 1, offset);
}

LValue MemberAccessExpression::evalLValueImpl(EvalContext& context) const {
    LValue lval = value().evalLValue(context);
    if (!lval)
        return nullptr;

    // TODO: handle unpacked unions
    int32_t offset = (int32_t)field.offset;
    if (value().type->isUnpackedStruct())
        return lval.selectIndex(offset);

    int32_t width = (int32_t)type->getBitWidth();
    return lval.selectRange({ width + offset - 1, offset });
}

bool MemberAccessExpression::verifyConstantImpl(EvalContext& context) const {
    return value().verifyConstant(context);
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
        context.setAttributes(*result, syntax->attributes);

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
        context.setAttributes(*expr, syntax->attributes);

    return *expr;
}

ConstantValue CallExpression::evalImpl(EvalContext& context) const {
    // Delegate system calls to their appropriate handler.
    if (isSystemCall())
        return std::get<1>(subroutine)->eval(context, arguments());

    // Evaluate all argument in the current stack frame.
    SmallVectorSized<ConstantValue, 8> args;
    for (auto arg : arguments()) {
        ConstantValue v = arg->eval(context);
        if (!v)
            return nullptr;
        args.emplace(std::move(v));
    }

    // Push a new stack frame, push argument values as locals.
    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    if (!context.pushFrame(symbol, sourceRange.start(), lookupLocation))
        return nullptr;

    span<const FormalArgumentSymbol* const> formals = symbol.arguments;
    for (size_t i = 0; i < formals.size(); i++)
        context.createLocal(formals[i], args[i]);

    context.createLocal(symbol.returnValVar);

    using ER = Statement::EvalResult;
    ER er = symbol.getBody(&context).eval(context);

    ConstantValue result = std::move(*context.findLocal(symbol.returnValVar));
    context.popFrame();

    if (er == ER::Fail)
        return nullptr;

    ASSERT(er == ER::Success || er == ER::Return);
    return result;
}

bool CallExpression::verifyConstantImpl(EvalContext& context) const {
    for (auto arg : arguments()) {
        if (!arg->verifyConstant(context))
            return false;
    }

    if (isSystemCall())
        return std::get<1>(subroutine)->verifyConstant(context, arguments());

    // TODO: implement all rules here
    const SubroutineSymbol& symbol = *std::get<0>(subroutine);
    if (!context.pushFrame(symbol, sourceRange.start(), lookupLocation))
        return false;

    bool result = symbol.getBody().verifyConstant(context);
    context.popFrame();
    return result;
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

Expression& DataTypeExpression::fromSyntax(Compilation& compilation, const DataTypeSyntax& syntax,
                                           const BindContext& context) {
    if ((context.flags & BindFlags::AllowDataType) == 0) {
        context.addDiag(diag::ExpectedExpression, syntax.sourceRange());
        return badExpr(compilation, nullptr);
    }

    const Type& type = compilation.getType(syntax, context.lookupLocation, context.scope);
    return *compilation.emplace<DataTypeExpression>(type, syntax.sourceRange());
}

ConstantValue DataTypeExpression::evalImpl(EvalContext&) const {
    return nullptr;
}

} // namespace slang