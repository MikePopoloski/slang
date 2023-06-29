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

Pattern& Pattern::bind(const PatternSyntax& syntax, const Type& targetType, VarMap& varMap,
                       ASTContext& context) {
    Pattern* result;
    switch (syntax.kind) {
        case SyntaxKind::ParenthesizedPattern:
            return bind(*syntax.as<ParenthesizedPatternSyntax>().pattern, targetType, varMap,
                        context);
        case SyntaxKind::WildcardPattern:
            result = &WildcardPattern::fromSyntax(syntax.as<WildcardPatternSyntax>(), context);
            break;
        case SyntaxKind::ExpressionPattern:
            result = &ConstantPattern::fromSyntax(syntax.as<ExpressionPatternSyntax>(), targetType,
                                                  context);
            break;
        case SyntaxKind::VariablePattern:
            result = &VariablePattern::fromSyntax(syntax.as<VariablePatternSyntax>(), targetType,
                                                  varMap, context);
            break;
        case SyntaxKind::TaggedPattern:
            result = &TaggedPattern::fromSyntax(syntax.as<TaggedPatternSyntax>(), targetType,
                                                varMap, context);
            break;
        case SyntaxKind::StructurePattern:
            result = &StructurePattern::fromSyntax(syntax.as<StructurePatternSyntax>(), targetType,
                                                   varMap, context);
            break;
        default:
            SLANG_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

void Pattern::createPlaceholderVars(const PatternSyntax& syntax, VarMap& varMap,
                                    ASTContext& context) {
    switch (syntax.kind) {
        case SyntaxKind::ParenthesizedPattern:
            createPlaceholderVars(*syntax.as<ParenthesizedPatternSyntax>().pattern, varMap,
                                  context);
            break;
        case SyntaxKind::VariablePattern:
            VariablePattern::fromSyntax(syntax.as<VariablePatternSyntax>(),
                                        context.getCompilation().getErrorType(), varMap, context);
            break;
        case SyntaxKind::TaggedPattern:
            if (auto pattern = syntax.as<TaggedPatternSyntax>().pattern)
                createPlaceholderVars(*pattern, varMap, context);
            break;
        case SyntaxKind::StructurePattern:
            for (auto member : syntax.as<StructurePatternSyntax>().members) {
                if (member->kind == SyntaxKind::NamedStructurePatternMember) {
                    createPlaceholderVars(*member->as<NamedStructurePatternMemberSyntax>().pattern,
                                          varMap, context);
                }
                else {
                    createPlaceholderVars(
                        *member->as<OrderedStructurePatternMemberSyntax>().pattern, varMap,
                        context);
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

    auto& expr = Expression::bindRValue(*type, *syntax.expr,
                                        syntax.expr->getFirstToken().location(), context);

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

Pattern& VariablePattern::fromSyntax(const VariablePatternSyntax& syntax, const Type& targetType,
                                     VarMap& varMap, ASTContext& context) {
    auto& comp = context.getCompilation();
    auto var = comp.emplace<PatternVarSymbol>(syntax.variableName.valueText(),
                                              syntax.variableName.location(), targetType);

    if (!var->name.empty()) {
        auto [it, inserted] = varMap.emplace(var->name, var);
        if (!inserted) {
            auto& diag = context.addDiag(diag::Redefinition, syntax.variableName.range());
            diag << var->name;
            diag.addNote(diag::NoteDeclarationHere, it->second->location);
            return badPattern(comp, nullptr);
        }

        var->nextTemp = std::exchange(context.firstTempVar, var);
    }

    // We need to force resolution here because the pattern variable doesn't
    // live in a scope and so later attempts at touching it could cause normal
    // resolution logic to fail.
    var->getDeclaredType()->forceResolveAt(context);
    return *comp.emplace<VariablePattern>(*var, syntax.sourceRange());
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

Pattern& TaggedPattern::fromSyntax(const TaggedPatternSyntax& syntax, const Type& targetType,
                                   VarMap& varMap, ASTContext& context) {
    auto& comp = context.getCompilation();
    if (!targetType.isTaggedUnion()) {
        if (!targetType.isError())
            context.addDiag(diag::PatternTaggedType, syntax.sourceRange()) << targetType;

        createPlaceholderVars(syntax, varMap, context);
        return badPattern(comp, nullptr);
    }

    auto memberName = syntax.memberName.valueText();
    auto member = targetType.getCanonicalType().as<Scope>().find(memberName);
    if (!member) {
        if (!memberName.empty()) {
            auto& diag = context.addDiag(diag::UnknownMember, syntax.memberName.range());
            diag << memberName << targetType;
        }

        createPlaceholderVars(syntax, varMap, context);
        return badPattern(comp, nullptr);
    }

    auto& field = member->as<FieldSymbol>();

    const Pattern* value = nullptr;
    if (syntax.pattern)
        value = &Pattern::bind(*syntax.pattern, field.getType(), varMap, context);

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

Pattern& StructurePattern::fromSyntax(const StructurePatternSyntax& syntax, const Type& targetType,
                                      VarMap& varMap, ASTContext& context) {
    auto& comp = context.getCompilation();
    if (!targetType.isStruct() || syntax.members.empty()) {
        if (!targetType.isError() && !syntax.members.empty())
            context.addDiag(diag::PatternStructType, syntax.sourceRange()) << targetType;

        createPlaceholderVars(syntax, varMap, context);
        return badPattern(comp, nullptr);
    }

    bool bad = false;
    auto& structScope = targetType.getCanonicalType().as<Scope>();

    SmallVector<FieldPattern, 4> patterns;
    if (syntax.members[0]->kind == SyntaxKind::OrderedStructurePatternMember) {
        auto fields = structScope.membersOfType<FieldSymbol>();
        auto it = fields.begin();
        for (auto memberSyntax : syntax.members) {
            auto& patternSyntax = *memberSyntax->as<OrderedStructurePatternMemberSyntax>().pattern;
            if (it == fields.end()) {
                if (!bad) {
                    context.addDiag(diag::PatternStructTooMany, memberSyntax->sourceRange())
                        << targetType;
                    bad = true;
                }

                createPlaceholderVars(patternSyntax, varMap, context);
                break;
            }

            auto& pattern = bind(patternSyntax, it->getType(), varMap, context);
            bad |= pattern.bad();

            patterns.push_back({&(*it), &pattern});
            it++;
        }

        if (it != fields.end()) {
            context.addDiag(diag::PatternStructTooFew, syntax.sourceRange()) << targetType;
            bad = true;
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

                createPlaceholderVars(*nspms.pattern, varMap, context);
                bad = true;
                continue;
            }

            auto& field = member->as<FieldSymbol>();
            auto& pattern = bind(*nspms.pattern, field.getType(), varMap, context);
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
