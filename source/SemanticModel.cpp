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

BoundExpression* SemanticModel::bindExpression(const ExpressionSyntax* syntax) {
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

        case SyntaxKind::AddExpression:
        case SyntaxKind::SubtractExpression:
        case SyntaxKind::MultiplyExpression:
        case SyntaxKind::DivideExpression:
        case SyntaxKind::ModExpression:
            return bindArithmeticExpression(syntax->as<BinaryExpressionSyntax>());

        case SyntaxKind::BinaryAndExpression:
        case SyntaxKind::BinaryOrExpression:
        case SyntaxKind::BinaryXorExpression:
        case SyntaxKind::BinaryXnorExpression:
            break;
    }
    return nullptr;
}

BoundExpression* SemanticModel::bindLiteral(const LiteralExpressionSyntax* syntax) {
    switch (syntax->kind) {
        case SyntaxKind::IntegerLiteralExpression: {
            ConstantValue cv = get<SVInt>(syntax->literal.numericValue());
            return alloc.emplace<BoundLiteralExpression>(syntax, getSpecialType(SpecialType::Int), cv);
        }
        default:
            return nullptr;
    }
}

BoundExpression* SemanticModel::bindArithmeticExpression(const BinaryExpressionSyntax* syntax) {
    BoundExpression* lhs = bindExpression(syntax->left);
    BoundExpression* rhs = bindExpression(syntax->right);

    //if (lhs->type->isReal || rhs->type->isReal)

    return alloc.emplace<BoundBinaryExpression>(syntax, nullptr, lhs, rhs);
}

const TypeSymbol* SemanticModel::getSpecialType(SpecialType type) const {
    return specialTypes[(int)type];
}

void SemanticModel::foldConstants(BoundExpression* expression) {
    ASSERT(expression);

    switch (expression->kind) {
        case BoundNodeKind::BinaryExpression: {
            auto binary = (BoundBinaryExpression*)expression;
            foldConstants(binary->left);
            foldConstants(binary->right);
            
            switch (binary->syntax->kind) {
                /*case SyntaxKind::AddExpression:
                    expression->constantValue = binary->left->constantValue + binary->right->constantValue;
                    break;
                case SyntaxKind::SubtractExpression:
                    expression->constantValue = binary->left->constantValue - binary->right->constantValue;
                    break;
                case SyntaxKind::MultiplyExpression:
                    expression->constantValue = binary->left->constantValue * binary->right->constantValue;
                    break;
                case SyntaxKind::DivideExpression:
                    expression->constantValue = binary->left->constantValue / binary->right->constantValue;
                    break;
                case SyntaxKind::ModExpression:
                    expression->constantValue = binary->left->constantValue % binary->right->constantValue;
                    break;*/
                default:
                    break;
            }
            break;
        }
        default:
            return;
    }
}

}