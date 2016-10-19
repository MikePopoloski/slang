#pragma once

#include "Symbol.h"
#include "SVInt.h"

namespace slang {

using ConstantValue = variant<SVInt, double>;

enum class BoundNodeKind {
    Unknown,
    LiteralExpression,
    BinaryExpression,
};

class BoundNode {
public:
    BoundNodeKind kind;

    BoundNode(BoundNodeKind kind) : kind(kind) {}
};

class BoundExpression : public BoundNode {
public:
    const ExpressionSyntax* syntax;
    const TypeSymbol* type;
    ConstantValue constantValue;

    BoundExpression(BoundNodeKind kind, const ExpressionSyntax* syntax, const TypeSymbol* type) :
        BoundNode(kind), syntax(syntax), type(type)
    {
    }
};

class BoundLiteralExpression : public BoundExpression {
public:
    BoundLiteralExpression(const ExpressionSyntax* syntax, const TypeSymbol* type, ConstantValue constantValue) :
        BoundExpression(BoundNodeKind::LiteralExpression, syntax, type)
    {
        this->constantValue = constantValue;
    }
};

class BoundBinaryExpression : public BoundExpression {
public:
    BoundExpression* left;
    BoundExpression* right;

    BoundBinaryExpression(const ExpressionSyntax* syntax, const TypeSymbol* type, BoundExpression* left, BoundExpression* right) :
        BoundExpression(BoundNodeKind::BinaryExpression, syntax, type), left(left), right(right)
    {
    }
};

class BoundParameterDeclaration : public BoundNode {
public:
    const ParameterDeclarationSyntax* syntax;
    BoundExpression* initializer;
    ConstantValue value;

    BoundParameterDeclaration(const ParameterDeclarationSyntax* syntax, BoundExpression* initializer) :
        BoundNode(BoundNodeKind::Unknown), syntax(syntax), initializer(initializer), value(initializer->constantValue)
    {
    }
};

}