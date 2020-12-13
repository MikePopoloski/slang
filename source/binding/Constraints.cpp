//------------------------------------------------------------------------------
// Constraints.cpp
// Constraint creation and analysis
//
// File is under the MIT license; see LICENSE for details
//------------------------------------------------------------------------------
#include "slang/binding/Constraints.h"

#include "slang/binding/Expression.h"
#include "slang/compilation/Compilation.h"
#include "slang/syntax/AllSyntax.h"

namespace slang {

const Constraint& Constraint::bind(const ConstraintItemSyntax& syntax, const BindContext& context) {
    BindContext ctx(context);
    ctx.flags &= ~BindFlags::ProceduralStatement;

    auto& comp = ctx.scope.getCompilation();
    Constraint* result;
    switch (syntax.kind) {
        case SyntaxKind::ConstraintBlock:
            result = &ConstraintList::fromSyntax(syntax.as<ConstraintBlockSyntax>(), ctx);
            break;
        case SyntaxKind::SolveBeforeConstraint:
        case SyntaxKind::DisableConstraint:
        case SyntaxKind::LoopConstraint:
        case SyntaxKind::ConditionalConstraint:
        case SyntaxKind::UniquenessConstraint:
        case SyntaxKind::ExpressionConstraint:
        case SyntaxKind::ImplicationConstraint:
            ctx.addDiag(diag::NotYetSupported, syntax.sourceRange());
            result = &badConstraint(comp, nullptr);
            break;
        default:
            THROW_UNREACHABLE;
    }

    result->syntax = &syntax;
    return *result;
}

Constraint& Constraint::badConstraint(Compilation& compilation, const Constraint* ctrl) {
    return *compilation.emplace<InvalidConstraint>(ctrl);
}

void InvalidConstraint::serializeTo(ASTSerializer& serializer) const {
    if (child)
        serializer.write("child", *child);
}

Constraint& ConstraintList::fromSyntax(const ConstraintBlockSyntax& syntax,
                                       const BindContext& context) {
    bool anyBad = false;
    SmallVectorSized<const Constraint*, 8> buffer;
    for (auto item : syntax.items) {
        auto& constraint = Constraint::bind(*item, context);
        buffer.append(&constraint);
        anyBad |= constraint.bad();
    }

    auto& comp = context.getCompilation();
    auto list = comp.emplace<ConstraintList>(buffer.copy(comp));
    if (anyBad)
        return badConstraint(comp, list);

    return *list;
}

void ConstraintList::serializeTo(ASTSerializer& serializer) const {
    serializer.startArray("list");
    for (auto constraint : list) {
        serializer.serialize(*constraint);
    }
    serializer.endArray();
}

} // namespace slang
