//------------------------------------------------------------------------------
// PatternExpressions.cpp
// Definitions for pattern expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/PatternExpressions.h"

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/AllTypes.h"
#include "slang/util/StackContainer.h"

namespace slang {

Expression& Expression::bindAssignmentPattern(Compilation& comp,
                                              const AssignmentPatternExpressionSyntax& syntax,
                                              const BindContext& context,
                                              const Type* assignmentTarget) {
    SourceRange range = syntax.sourceRange();

    if (syntax.type) {
        assignmentTarget = &comp.getType(*syntax.type, context.getLocation(), context.scope);
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
                THROW_UNREACHABLE;
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
                THROW_UNREACHABLE;
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
                THROW_UNREACHABLE;
        }
    }
}

ConstantValue AssignmentPatternExpressionBase::evalImpl(EvalContext& context) const {
    if (type->isIntegral()) {
        SmallVectorSized<SVInt, 8> values;
        for (auto elem : elements()) {
            ConstantValue v = elem->eval(context);
            if (!v)
                return nullptr;

            values.append(v.integer());
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
            ASSERT(setter.expr && setter.index);
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
        for (auto elem : elements()) {
            result.emplace_back(elem->eval(context));
            if (result.back().bad())
                return nullptr;
        }

        result.resizeToBound();
        return result;
    }
    else {
        std::vector<ConstantValue> values;
        for (auto elem : elements()) {
            values.emplace_back(elem->eval(context));
            if (values.back().bad())
                return nullptr;
        }

        return values;
    }
}

bool AssignmentPatternExpressionBase::verifyConstantImpl(EvalContext& context) const {
    for (auto elem : elements()) {
        if (!elem->verifyConstant(context))
            return false;
    }
    return true;
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
        auto& expr = Expression::bindRValue(*types[index++], *item,
                                            item->getFirstToken().location(), context);
        elems.append(&expr);
        bad |= expr.bad();
    }

    auto result =
        comp.emplace<SimpleAssignmentPatternExpression>(type, elems.copy(comp), sourceRange);
    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& SimpleAssignmentPatternExpression::forFixedArray(
    Compilation& comp, const SimpleAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Type& elementType, bitwidth_t numElements, SourceRange sourceRange) {

    bool bad = false;
    SmallVectorSized<const Expression*, 8> elems;
    for (auto item : syntax.items) {
        auto& expr =
            Expression::bindRValue(elementType, *item, item->getFirstToken().location(), context);
        elems.append(&expr);
        bad |= expr.bad();
    }

    if (!bad && numElements != syntax.items.size()) {
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

Expression& SimpleAssignmentPatternExpression::forDynamicArray(
    Compilation& comp, const SimpleAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    bool bad = false;
    SmallVectorSized<const Expression*, 8> elems;
    for (auto item : syntax.items) {
        auto& expr =
            Expression::bindRValue(elementType, *item, item->getFirstToken().location(), context);
        elems.append(&expr);
        bad |= expr.bad();
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

    // TODO: check that all memberMap entries are used

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
                results.append(&Expression::bindRValue(
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
            results.append(&Expression::bindRValue(
                type, *defaultSyntax, defaultSyntax->getFirstToken().location(), context));
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

    // TODO: check that all indexMap entries are used

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
                return &Expression::bindRValue(elementType, *defaultSyntax,
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
            return &Expression::bindRValue(elementType, *defaultSyntax,
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

    // TODO: check for duplicate keys
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
                auto& expr = bindRValue(member->as<FieldSymbol>().getType(), *item->expr,
                                        nameToken.location(), context);
                bad |= expr.bad();

                memberMap.emplace(member, &expr);
                memberSetters.emplace(MemberSetter{ member, &expr });
            }
            else {
                auto found = Lookup::unqualified(context.scope, name, LookupFlags::Type);
                if (found && found->isType()) {
                    auto& expr =
                        bindRValue(found->as<Type>(), *item->expr, nameToken.location(), context);
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
            const Type& typeKey =
                comp.getType(item->key->as<DataTypeSyntax>(), context.getLocation(), context.scope);
            if (typeKey.isSimpleType()) {
                auto& expr = bindRValue(typeKey, *item->expr,
                                        item->expr->getFirstToken().location(), context);

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

Expression& StructuredAssignmentPatternExpression::forFixedArray(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    // TODO: check for duplicate keys
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
            const Type& typeKey =
                comp.getType(item->key->as<DataTypeSyntax>(), context.getLocation(), context.scope);
            if (typeKey.isSimpleType()) {
                auto& expr = bindRValue(typeKey, *item->expr,
                                        item->expr->getFirstToken().location(), context);

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

            if (!type.getFixedRange().containsPoint(*index)) {
                auto& diag = context.addDiag(diag::IndexValueInvalid, indexExpr.sourceRange);
                diag << *index;
                diag << type;
                bad = true;
                continue;
            }

            auto& expr = bindRValue(elementType, *item->expr,
                                    item->expr->getFirstToken().location(), context);
            bad |= expr.bad();

            indexMap.emplace(*index, &expr);
            indexSetters.append(IndexSetter{ &indexExpr, &expr });
        }
    }

    SmallVectorSized<const Expression*, 8> elements;
    bad |= matchElements(context, elementType, type.getFixedRange(), syntax.sourceRange(), indexMap,
                         typeSetters, defaultSetter, elements);

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, span<const MemberSetter>{}, typeSetters.copy(comp), indexSetters.copy(comp),
        defaultSetter, elements.copy(comp), sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& StructuredAssignmentPatternExpression::forDynamicArray(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    // TODO: check for duplicate keys
    bool bad = false;
    SmallVectorSized<const Expression*, 8> elements;
    SmallVectorSized<IndexSetter, 4> indexSetters;

    for (auto item : syntax.items) {
        if (item->key->kind == SyntaxKind::DefaultPatternKeyExpression) {
            context.addDiag(diag::AssignmentPatternDynamicDefault, item->key->sourceRange());
            bad = true;
        }
        else if (DataTypeSyntax::isKind(item->key->kind)) {
            context.addDiag(diag::AssignmentPatternDynamicType, item->key->sourceRange());
            bad = true;
        }
        else {
            // TODO: check for type name here

            auto& indexExpr = Expression::bind(*item->key, context, BindFlags::Constant);
            optional<int32_t> index = context.evalInteger(indexExpr);
            if (!index) {
                bad = true;
                continue;
            }

            // TODO: check gt zero

            auto& expr = bindRValue(elementType, *item->expr,
                                    item->expr->getFirstToken().location(), context);
            bad |= expr.bad();

            indexSetters.append(IndexSetter{ &indexExpr, &expr });

            size_t i = size_t(*index);
            if (i >= elements.size())
                elements.extend(i - elements.size() + 1);
            elements[i] = &expr;
        }
    }

    // TODO: check that all elements have expressions assigned

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, span<const MemberSetter>{}, span<const TypeSetter>{}, indexSetters.copy(comp),
        nullptr, elements.copy(comp), sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

Expression& StructuredAssignmentPatternExpression::forAssociativeArray(
    Compilation& comp, const StructuredAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    // TODO: check for duplicate keys
    bool bad = false;
    const Expression* defaultSetter = nullptr;
    SmallVectorSized<IndexSetter, 4> indexSetters;

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
            // TODO: check for type name here

            const Expression* indexExpr;
            if (indexType) {
                indexExpr =
                    &bindRValue(*indexType, *item->key, item->key->getFirstToken().location(),
                                context.resetFlags(BindFlags::Constant));
            }
            else {
                indexExpr = &Expression::bind(*item->key, context, BindFlags::Constant);
            }

            // TODO: check constant index value for validity

            auto& expr = bindRValue(elementType, *item->expr,
                                    item->expr->getFirstToken().location(), context);
            bad |= expr.bad() || indexExpr->bad();

            indexSetters.append(IndexSetter{ indexExpr, &expr });
        }
    }

    auto result = comp.emplace<StructuredAssignmentPatternExpression>(
        type, span<const MemberSetter>{}, span<const TypeSetter>{}, indexSetters.copy(comp),
        defaultSetter, span<const Expression*>{}, sourceRange);

    if (bad)
        return badExpr(comp, result);

    return *result;
}

void StructuredAssignmentPatternExpression::serializeTo(ASTSerializer&) const {
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

    size_t count = 0;
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
            auto& expr = Expression::bindRValue(*types[index++], *item,
                                                item->getFirstToken().location(), context);
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

Expression& ReplicatedAssignmentPatternExpression::forFixedArray(
    Compilation& comp, const ReplicatedAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Type& elementType, bitwidth_t numElements, SourceRange sourceRange) {

    size_t count = 0;
    auto& countExpr = bindReplCount(comp, *syntax.countExpr, context, count);
    if (countExpr.bad())
        return badExpr(comp, nullptr);

    bool bad = false;
    SmallVectorSized<const Expression*, 8> elems;
    for (size_t i = 0; i < count; i++) {
        for (auto item : syntax.items) {
            auto& expr = Expression::bindRValue(elementType, *item,
                                                item->getFirstToken().location(), context);
            elems.append(&expr);
            bad |= expr.bad();
        }
    }

    if (!bad && numElements != elems.size()) {
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

Expression& ReplicatedAssignmentPatternExpression::forDynamicArray(
    Compilation& comp, const ReplicatedAssignmentPatternSyntax& syntax, const BindContext& context,
    const Type& type, const Type& elementType, SourceRange sourceRange) {

    size_t count = 0;
    auto& countExpr = bindReplCount(comp, *syntax.countExpr, context, count);
    if (countExpr.bad())
        return badExpr(comp, nullptr);

    bool bad = false;
    SmallVectorSized<const Expression*, 8> elems;
    for (size_t i = 0; i < count; i++) {
        for (auto item : syntax.items) {
            auto& expr = Expression::bindRValue(elementType, *item,
                                                item->getFirstToken().location(), context);
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

void ReplicatedAssignmentPatternExpression::serializeTo(ASTSerializer& serializer) const {
    serializer.write("count", count());
    AssignmentPatternExpressionBase::serializeTo(serializer);
}

} // namespace slang
