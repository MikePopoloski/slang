#include "SemanticModel.h"

#include "SyntaxTree.h"

namespace slang {

SemanticModel::SemanticModel(DeclarationTable& declTable) {
}

void SemanticModel::bindModuleImplicit(ModuleDeclarationSyntax* module) {
}

BoundParameterDeclaration* SemanticModel::bindParameterDecl(ParameterDeclarationStatementSyntax* syntax) {
    ASSERT(syntax);
    ASSERT(syntax->parameter);
    ASSERT(syntax->parameter->kind == SyntaxKind::ParameterDeclaration);

    auto param = syntax->parameter->as<ParameterDeclarationSyntax>();
    auto declarator = param->declarators[0];
    auto initializer = declarator->initializer;

    auto boundInitializer = bindValue(initializer->expr, ValueCategory::SelfDetermined);

    return alloc.emplace<BoundParameterDeclaration>();
}

BoundExpression* SemanticModel::bindValue(ExpressionSyntax* syntax, ValueCategory category) {
    auto expr = bindExpression(syntax);
    return expr;
}

BoundExpression* SemanticModel::bindExpression(ExpressionSyntax* syntax) {
    ASSERT(syntax);

    switch (syntax->kind) {
        case SyntaxKind::NullLiteralExpression:
        case SyntaxKind::StringLiteralExpression:
        case SyntaxKind::RealLiteralExpression:
        case SyntaxKind::TimeLiteralExpression:
        case SyntaxKind::WildcardLiteralExpression:
        case SyntaxKind::OneStepLiteralExpression:
        case SyntaxKind::IntegerLiteralExpression:
        case SyntaxKind::UnbasedUnsizedLiteralExpression:
            //return bindLiteral(syntax->as<LiteralExpressionSyntax>());
        case SyntaxKind::IntegerVectorExpression:
            //return bindVectorLiteral(syntax->as<IntegerVectorExpressionSyntax>());
        case SyntaxKind::ParenthesizedExpression:
            break;
    }
    return nullptr;
}

}