#include "SemanticModel.h"

#include "SyntaxTree.h"

namespace slang {

SemanticModel::SemanticModel() {
    specialTypes[(int)SpecialType::Int] = alloc.emplace<IntegralTypeSymbol>(true, 32);
}

SemanticModel::SemanticModel(DeclarationTable& declTable) :
    SemanticModel()
{
}

void SemanticModel::bindModuleImplicit(ModuleDeclarationSyntax* module) {
}

BoundParameterDeclaration* SemanticModel::bindParameterDecl(const ParameterDeclarationSyntax* syntax) {
    ASSERT(syntax);
    ASSERT(syntax->kind == SyntaxKind::ParameterDeclaration);

    auto declarator = syntax->declarators[0];
    auto initializer = declarator->initializer;

    auto boundInitializer = bindExpression(initializer->expr);
    foldConstants(boundInitializer);

    return alloc.emplace<BoundParameterDeclaration>(syntax, boundInitializer);
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
        case SyntaxKind::UnbasedUnsizedLiteralExpression:
            //return bindLiteral(syntax->as<LiteralExpressionSyntax>());
        case SyntaxKind::IntegerVectorExpression:
            //return bindVectorLiteral(syntax->as<IntegerVectorExpressionSyntax>());
        case SyntaxKind::ParenthesizedExpression:
            break;
        case SyntaxKind::IntegerLiteralExpression:
            return bindLiteral(syntax->as<LiteralExpressionSyntax>());
    }
    return nullptr;
}

BoundExpression* SemanticModel::bindLiteral(const LiteralExpressionSyntax* syntax) {
    switch (syntax->kind) {
        case SyntaxKind::IntegerLiteralExpression: {
            // the integer has already been checked for overflow in the parser
            ConstantValue cv((int32_t)syntax->literal.numericValue().integer);
            return alloc.emplace<BoundExpression>(syntax, getSpecialType(SpecialType::Int), cv);
        }
        default:
            return nullptr;
    }
}

const TypeSymbol* SemanticModel::getSpecialType(SpecialType type) const {
    return specialTypes[(int)type];
}

void SemanticModel::foldConstants(BoundExpression* expression) {
    switch (expression->syntax->kind) {
        default:
            break;
    }
}

}