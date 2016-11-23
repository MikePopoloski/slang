#pragma once

#include "SVInt.h"
#include "Symbol.h"

namespace slang {

class TypeSymbol;

using ConstantValue = std::variant<SVInt, double>;

enum class BoundNodeKind {
    Unknown,
    Literal,
    Parameter,
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

class BadBoundExpression : public BoundExpression {
public:
    BadBoundExpression() :
        BoundExpression(BoundNodeKind::Unknown, nullptr, nullptr, true)
    {
    }
};

class BoundLiteral : public BoundExpression {
public:
    BoundLiteral(const ExpressionSyntax* syntax, const TypeSymbol* type, bool bad) :
        BoundExpression(BoundNodeKind::Literal, syntax, type, bad)
    {
    }
};

class BoundParameter : public BoundExpression {
public:
    const ParameterSymbol& symbol;

    BoundParameter(const ExpressionSyntax* syntax, const ParameterSymbol& symbol, bool bad) :
        BoundExpression(BoundNodeKind::Parameter, syntax, symbol.type, bad), symbol(symbol)
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