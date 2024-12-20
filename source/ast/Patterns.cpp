//------------------------------------------------------------------------------
// Patterns.cpp
// AST definitions for pattern matching
//
// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//------------------------------------------------------------------------------
#include "slang/ast/Patterns.h"

#include "slang/ast/ASTSerializer.h"
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/syntax/AllSyntax.h"

namespace {

using namespace slang;
using namespace slang::ast;

struct EvalVisitor {
    template<typename T>
    ConstantValue visit(const T& pattern, EvalContext& context, const ConstantValue& value,
                        CaseStatementCondition conditionKind) {
        if (pattern.bad())
            return nullptr;

        return pattern.evalImpl(context, value, conditionKind);
    }
};

} // namespace

namespace slang::ast {

using namespace syntax;

Pattern& Pattern::bind(const ASTContext& context, const syntax::PatternSyntax& syntax,
                       const Type& targetType) {
    Pattern* result;
    switch (syntax.kind) {
        case SyntaxKind::ParenthesizedPattern:
            return bind(context, *syntax.as<ParenthesizedPatternSyntax>().pattern, targetType);
        case SyntaxKind::WildcardPattern:
            result = &WildcardPattern::fromSyntax(syntax.as<WildcardPatternSyntax>(), context);
            break;
        case SyntaxKind::ExpressionPattern:
            result = &ConstantPattern::fromSyntax(syntax.as<ExpressionPatternSyntax>(), targetType,
                                                  context);
            break;
        case SyntaxKind::VariablePattern:
            result = &VariablePattern::fromSyntax(syntax.as<VariablePatternSyntax>(), context);
            break;
        case SyntaxKind::TaggedPattern:
            result = &TaggedPattern::fromSyntax(syntax.as<TaggedPatternSyntax>(), targetType,
                                                context);
            break;
        case SyntaxKind::StructurePattern:
            result = &StructurePattern::fromSyntax(syntax.as<StructurePatternSyntax>(), targetType,
                                                   context);
            break;
        default:
            SLANG_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

bool Pattern::createPatternVars(const ASTContext& context, const PatternSyntax& patternSyntax,
                                const ExpressionSyntax& condSyntax,
                                SmallVector<const PatternVarSymbol*>& results) {
    auto& expr = Expression::bind(condSyntax, context);
    if (expr.bad())
        return false;

    return createPatternVars(context, patternSyntax, *expr.type, results);
}

bool Pattern::createPatternVars(const ASTContext& context, const PatternSyntax& syntax,
                                const Type& targetType,
                                SmallVector<const PatternVarSymbol*>& results) {
    switch (syntax.kind) {
        case SyntaxKind::ParenthesizedPattern:
            return createPatternVars(context, *syntax.as<ParenthesizedPatternSyntax>().pattern,
                                     targetType, results);
        case SyntaxKind::VariablePattern: {
            auto& varSyntax = syntax.as<VariablePatternSyntax>();
            auto var = context.getCompilation().emplace<PatternVarSymbol>(
                varSyntax.variableName.valueText(), varSyntax.variableName.location(), targetType);
            var->setSyntax(varSyntax);
            results.push_back(var);
            break;
        }
        case SyntaxKind::TaggedPattern:
            return TaggedPattern::createVars(context, syntax.as<TaggedPatternSyntax>(), targetType,
                                             results);
        case SyntaxKind::StructurePattern:
            return StructurePattern::createVars(context, syntax.as<StructurePatternSyntax>(),
                                                targetType, results);
        default:
            break;
    }

    return true;
}

void Pattern::createPlaceholderVars(const ASTContext& context, const PatternSyntax& syntax,
                                    SmallVector<const PatternVarSymbol*>& results) {
    switch (syntax.kind) {
        case SyntaxKind::ParenthesizedPattern:
            createPlaceholderVars(context, *syntax.as<ParenthesizedPatternSyntax>().pattern,
                                  results);
            break;
        case SyntaxKind::VariablePattern: {
            auto& comp = context.getCompilation();
            auto& varSyntax = syntax.as<VariablePatternSyntax>();
            auto var = comp.emplace<PatternVarSymbol>(varSyntax.variableName.valueText(),
                                                      varSyntax.variableName.location(),
                                                      comp.getErrorType());
            var->setSyntax(varSyntax);
            results.push_back(var);
            break;
        }
        case SyntaxKind::TaggedPattern:
            if (auto pattern = syntax.as<TaggedPatternSyntax>().pattern)
                createPlaceholderVars(context, *pattern, results);
            break;
        case SyntaxKind::StructurePattern:
            for (auto member : syntax.as<StructurePatternSyntax>().members) {
                if (member->kind == SyntaxKind::NamedStructurePatternMember) {
                    createPlaceholderVars(context,
                                          *member->as<NamedStructurePatternMemberSyntax>().pattern,
                                          results);
                }
                else {
                    createPlaceholderVars(
                        context, *member->as<OrderedStructurePatternMemberSyntax>().pattern,
                        results);
                }
            }
            break;
        default:
            break;
    }
}

ConstantValue Pattern::eval(EvalContext& context, const ConstantValue& value,
                            CaseStatementCondition conditionKind) const {
    EvalVisitor visitor;
    return visit(visitor, context, value, conditionKind);
}

Pattern& Pattern::badPattern(Compilation& comp, const Pattern* child) {
    return *comp.emplace<InvalidPattern>(child);
}

void InvalidPattern::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

Pattern& WildcardPattern::fromSyntax(const WildcardPatternSyntax& syntax,
                                     const ASTContext& context) {
    auto& comp = context.getCompilation();
    return *comp.emplace<WildcardPattern>(syntax.sourceRange());
}

ConstantValue WildcardPattern::evalImpl(EvalContext&, const ConstantValue&,
                                        CaseStatementCondition) const {
    // Always succeeds.
    return SVInt(1, 1, false);
}

Pattern& ConstantPattern::fromSyntax(const ExpressionPatternSyntax& syntax, const Type& targetType,
                                     const ASTContext& context) {
    // Bind the expression (it must be a constant).
    // We force integral types to be four-state here so that if we need to do a casex / casez
    // condition we will get the right result for unknowns.
    auto& comp = context.getCompilation();
    const Type* type = &targetType;
    if (type->isIntegral() && !type->isFourState()) {
        auto flags = type->getIntegralFlags() | IntegralFlags::FourState;
        type = &comp.getType(type->getBitWidth(), flags);
    }

    auto& expr = Expression::bindRValue(*type, *syntax.expr, {}, context);
    if (expr.bad() || !context.eval(expr))
        return badPattern(comp, nullptr);

    return *comp.emplace<ConstantPattern>(expr, syntax.sourceRange());
}

ConstantValue ConstantPattern::evalImpl(EvalContext&, const ConstantValue& value,
                                        CaseStatementCondition conditionKind) const {
    SLANG_ASSERT(expr.constant);
    SLANG_ASSERT(conditionKind != CaseStatementCondition::Inside);

    bool result;
    if (conditionKind == CaseStatementCondition::Normal || !expr.constant->isInteger() ||
        !value.isInteger()) {
        result = *expr.constant == value;
    }
    else {
        const SVInt& l = expr.constant->integer();
        const SVInt& r = value.integer();
        if (conditionKind == CaseStatementCondition::WildcardJustZ)
            result = caseZWildcardEqual(l, r);
        else
            result = caseXWildcardEqual(l, r);
    }

    return SVInt(1, result ? 1 : 0, false);
}

void ConstantPattern::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
}

Pattern& VariablePattern::fromSyntax(const VariablePatternSyntax& syntax,
                                     const ASTContext& context) {
    // The pattern var has already been created in our scope, so just look it up.
    auto& comp = context.getCompilation();
    auto name = syntax.variableName.valueText();
    auto currVar = context.firstTempVar;
    while (currVar) {
        if (currVar->name == name && currVar->kind == SymbolKind::PatternVar) {
            return *comp.emplace<VariablePattern>(currVar->as<PatternVarSymbol>(),
                                                  syntax.sourceRange());
        }
        currVar = currVar->nextTemp;
    }

    auto var = context.scope->find(name);
    if (!var || var->kind != SymbolKind::PatternVar || var->getSyntax() != &syntax) {
        // Some other error has occurred, likely a duplicate name,
        // so just return an error.
        return badPattern(comp, nullptr);
    }

    return *comp.emplace<VariablePattern>(var->as<PatternVarSymbol>(), syntax.sourceRange());
}

ConstantValue VariablePattern::evalImpl(EvalContext& context, const ConstantValue& value,
                                        CaseStatementCondition) const {
    // Capture the current value into a local for our symbol.
    context.createLocal(&variable, value);

    // Always succeeds.
    return SVInt(1, 1, false);
}

void VariablePattern::serializeTo(ASTSerializer& serializer) const {
    serializer.write("variable", variable);
}

bool TaggedPattern::createVars(const ASTContext& context, const syntax::TaggedPatternSyntax& syntax,
                               const Type& targetType,
                               SmallVector<const PatternVarSymbol*>& results) {
    if (!targetType.isTaggedUnion()) {
        if (!targetType.isError())
            context.addDiag(diag::PatternTaggedType, syntax.sourceRange()) << targetType;

        createPlaceholderVars(context, syntax, results);
        return false;
    }

    auto memberName = syntax.memberName.valueText();
    auto member = targetType.getCanonicalType().as<Scope>().find(memberName);
    if (!member) {
        if (!memberName.empty()) {
            auto& diag = context.addDiag(diag::UnknownMember, syntax.memberName.range());
            diag << memberName << targetType;
        }

        createPlaceholderVars(context, syntax, results);
        return false;
    }

    if (!syntax.pattern)
        return true;

    auto& field = member->as<FieldSymbol>();
    return createPatternVars(context, *syntax.pattern, field.getType(), results);
}

Pattern& TaggedPattern::fromSyntax(const TaggedPatternSyntax& syntax, const Type& targetType,
                                   const ASTContext& context) {
    SLANG_ASSERT(targetType.isTaggedUnion());

    auto memberName = syntax.memberName.valueText();
    auto member = targetType.getCanonicalType().as<Scope>().find(memberName);
    SLANG_ASSERT(member);

    auto& field = member->as<FieldSymbol>();

    const Pattern* value = nullptr;
    if (syntax.pattern)
        value = &Pattern::bind(context, *syntax.pattern, field.getType());

    auto& comp = context.getCompilation();
    auto result = comp.emplace<TaggedPattern>(field, value, syntax.sourceRange());
    if (value && value->bad())
        return badPattern(comp, result);

    return *result;
}

ConstantValue TaggedPattern::evalImpl(EvalContext& context, const ConstantValue& value,
                                      CaseStatementCondition conditionKind) const {
    if (value.bad())
        return nullptr;

    // Check if the union's active member matches the one in our pattern.
    auto& unionVal = value.unionVal();
    if (unionVal->activeMember != member.fieldIndex)
        return SVInt(1, 0, false);

    if (valuePattern)
        return valuePattern->eval(context, unionVal->value, conditionKind);

    // If no nested pattern we just succeed.
    return SVInt(1, 1, false);
}

void TaggedPattern::serializeTo(ASTSerializer& serializer) const {
    serializer.writeLink("member", member);
    if (valuePattern)
        serializer.write("valuePattern", *valuePattern);
}

bool StructurePattern::createVars(const ASTContext& context,
                                  const syntax::StructurePatternSyntax& syntax,
                                  const Type& targetType,
                                  SmallVector<const PatternVarSymbol*>& results) {
    if (!targetType.isStruct() || syntax.members.empty()) {
        if (!targetType.isError() && !syntax.members.empty())
            context.addDiag(diag::PatternStructType, syntax.sourceRange()) << targetType;

        createPlaceholderVars(context, syntax, results);
        return false;
    }

    bool result = true;
    auto& structScope = targetType.getCanonicalType().as<Scope>();

    if (syntax.members[0]->kind == SyntaxKind::OrderedStructurePatternMember) {
        auto fields = structScope.membersOfType<FieldSymbol>();
        auto it = fields.begin();
        for (auto memberSyntax : syntax.members) {
            auto& patternSyntax = *memberSyntax->as<OrderedStructurePatternMemberSyntax>().pattern;
            if (it == fields.end()) {
                if (result) {
                    context.addDiag(diag::PatternStructTooMany, memberSyntax->sourceRange())
                        << targetType;
                    result = false;
                }

                createPlaceholderVars(context, patternSyntax, results);
                continue;
            }

            result &= createPatternVars(context, patternSyntax, it->getType(), results);
            it++;
        }

        if (it != fields.end()) {
            context.addDiag(diag::PatternStructTooFew, syntax.sourceRange()) << targetType;
            result = false;
        }
    }
    else {
        for (auto memberSyntax : syntax.members) {
            auto& nspms = memberSyntax->as<NamedStructurePatternMemberSyntax>();
            auto memberName = nspms.name.valueText();
            auto member = structScope.find(memberName);
            if (!member) {
                if (!memberName.empty()) {
                    auto& diag = context.addDiag(diag::UnknownMember, nspms.name.range());
                    diag << memberName << targetType;
                }

                createPlaceholderVars(context, *nspms.pattern, results);
                result = false;
                continue;
            }

            auto& field = member->as<FieldSymbol>();
            result &= createPatternVars(context, *nspms.pattern, field.getType(), results);
        }
    }

    return result;
}

Pattern& StructurePattern::fromSyntax(const StructurePatternSyntax& syntax, const Type& targetType,
                                      const ASTContext& context) {
    auto& comp = context.getCompilation();
    SLANG_ASSERT(targetType.isStruct() && !syntax.members.empty());

    bool bad = false;
    auto& structScope = targetType.getCanonicalType().as<Scope>();

    SmallVector<FieldPattern, 4> patterns;
    if (syntax.members[0]->kind == SyntaxKind::OrderedStructurePatternMember) {
        auto fields = structScope.membersOfType<FieldSymbol>();
        auto it = fields.begin();
        for (auto memberSyntax : syntax.members) {
            SLANG_ASSERT(it != fields.end());

            auto& patternSyntax = *memberSyntax->as<OrderedStructurePatternMemberSyntax>().pattern;
            auto& pattern = bind(context, patternSyntax, it->getType());
            bad |= pattern.bad();

            patterns.push_back({&(*it), &pattern});
            it++;
        }

        SLANG_ASSERT(it == fields.end());
    }
    else {
        for (auto memberSyntax : syntax.members) {
            auto& nspms = memberSyntax->as<NamedStructurePatternMemberSyntax>();
            auto memberName = nspms.name.valueText();
            auto member = structScope.find(memberName);
            SLANG_ASSERT(member);

            auto& field = member->as<FieldSymbol>();
            auto& pattern = bind(context, *nspms.pattern, field.getType());
            bad |= pattern.bad();

            patterns.push_back({&field, &pattern});
        }
    }

    auto result = comp.emplace<StructurePattern>(patterns.copy(comp), syntax.sourceRange());
    if (bad)
        return badPattern(comp, result);

    return *result;
}

ConstantValue StructurePattern::evalImpl(EvalContext& context, const ConstantValue& value,
                                         CaseStatementCondition conditionKind) const {
    if (value.bad())
        return nullptr;

    if (value.isUnpacked()) {
        auto elems = value.elements();
        for (auto& fp : patterns) {
            auto cv = fp.pattern->eval(context, elems[fp.field->fieldIndex], conditionKind);
            if (!cv.isTrue())
                return cv;
        }
    }
    else {
        auto& cvi = value.integer();
        for (auto& fp : patterns) {
            int32_t io = (int32_t)fp.field->bitOffset;
            int32_t width = (int32_t)fp.field->getType().getBitWidth();

            auto cv = fp.pattern->eval(context, cvi.slice(width + io - 1, io), conditionKind);
            if (!cv.isTrue())
                return cv;
        }
    }

    return SVInt(1, 1, false);
}

void StructurePattern::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("patterns");
    for (auto& fp : patterns) {
        serializer.startObject();
        serializer.writeLink("field", *fp.field);
        serializer.write("pattern", *fp.pattern);
        serializer.endObject();
    }
    serializer.endArray();
}

} // namespace slang::ast
