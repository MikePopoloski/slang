#pragma once

#include "SVInt.h"

namespace slang {

class TypeSymbol;

using ConstantValue = variant<SVInt, double>;

enum class BoundNodeKind {
    Unknown,
    LiteralExpression,
    UnaryExpression,
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
    bool bad;

    BoundExpression(BoundNodeKind kind, const ExpressionSyntax* syntax, const TypeSymbol* type, bool bad) :
        BoundNode(kind), syntax(syntax), type(type), bad(bad)
    {
    }
};

class BoundLiteralExpression : public BoundExpression {
public:
    BoundLiteralExpression(const ExpressionSyntax* syntax, const TypeSymbol* type, bool bad) :
        BoundExpression(BoundNodeKind::LiteralExpression, syntax, type, bad)
    {
    }
};

class BoundUnaryExpression : public BoundExpression {
public:
    BoundExpression* operand;

    BoundUnaryExpression(const ExpressionSyntax* syntax, const TypeSymbol* type, BoundExpression* operand, bool bad) :
        BoundExpression(BoundNodeKind::UnaryExpression, syntax, type, bad), operand(operand)
    {
    }
};

class BoundBinaryExpression : public BoundExpression {
public:
    BoundExpression* left;
    BoundExpression* right;

    BoundBinaryExpression(const ExpressionSyntax* syntax, const TypeSymbol* type, BoundExpression* left, BoundExpression* right, bool bad) :
        BoundExpression(BoundNodeKind::BinaryExpression, syntax, type, bad), left(left), right(right)
    {
    }
};

}