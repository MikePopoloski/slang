#pragma once

#include "ConstantValue.h"
#include "Symbol.h"

namespace slang {

class BoundNode {
};

class BoundExpression : public BoundNode {
public:
    const ExpressionSyntax* syntax;
    const TypeSymbol* type;
    ConstantValue constantValue;

    BoundExpression(const ExpressionSyntax* syntax, const TypeSymbol* type, ConstantValue constantValue) :
        syntax(syntax), type(type), constantValue(constantValue)
    {
    }
};

class BoundParameterDeclaration : public BoundNode {
public:
    const ParameterDeclarationSyntax* syntax;
    const BoundExpression* initializer;
    ConstantValue value;

    BoundParameterDeclaration(const ParameterDeclarationSyntax* syntax, const BoundExpression* initializer) :
        syntax(syntax), initializer(initializer), value(initializer->constantValue)
    {
    }
};

}