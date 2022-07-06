//------------------------------------------------------------------------------
// PatternExpressions.cpp
// Definitions for pattern expressions
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/Patterns.h"

#include "slang/compilation/Compilation.h"
#include "slang/diagnostics/ExpressionsDiags.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/symbols/ASTSerializer.h"
#include "slang/symbols/VariableSymbols.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/types/AllTypes.h"

namespace slang {

Pattern& Pattern::bind(const PatternSyntax& syntax, const Type& targetType, VarMap& varMap,
                       BindContext& context) {
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
        case SyntaxKind::StructurePattern:
        default:
            THROW_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

Pattern& Pattern::badPattern(Compilation& comp, const Pattern* pattern) {
    return *comp.emplace<InvalidPattern>(pattern);
}

void InvalidPattern::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

Pattern& WildcardPattern::fromSyntax(const WildcardPatternSyntax& syntax,
                                     const BindContext& context) {
    auto& comp = context.getCompilation();
    return *comp.emplace<WildcardPattern>(syntax.sourceRange());
}

Pattern& ConstantPattern::fromSyntax(const ExpressionPatternSyntax& syntax, const Type& targetType,
                                     const BindContext& context) {
    // Bind the expression (it must be a constant).
    auto& comp = context.getCompilation();
    auto& expr = Expression::bind(*syntax.expr, context);
    if (expr.bad() || !context.eval(expr))
        return badPattern(comp, nullptr);

    if (!expr.type->isEquivalent(targetType)) {
        auto& diag = context.addDiag(diag::PatternTypeMismatch, expr.sourceRange);
        diag << *expr.type << targetType;
        return badPattern(comp, nullptr);
    }

    return *comp.emplace<WildcardPattern>(syntax.sourceRange());
}

void ConstantPattern::serializeTo(ASTSerializer& serializer) const {
    serializer.write("expr", expr);
}

Pattern& VariablePattern::fromSyntax(const VariablePatternSyntax& syntax, const Type& targetType,
                                     VarMap& varMap, BindContext& context) {
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

    return *comp.emplace<VariablePattern>(*var, syntax.sourceRange());
}

void VariablePattern::serializeTo(ASTSerializer& serializer) const {
    serializer.write("variable", variable);
}

} // namespace slang
