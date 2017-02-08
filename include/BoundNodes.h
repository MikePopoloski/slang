#pragma once

#include "ConstantValue.h"
#include "Symbol.h"

namespace slang {

class TypeSymbol;

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

    bool bad() const { return kind == BoundNodeKind::Unknown; }
};

class BoundExpression : public BoundNode {
public:
    const ExpressionSyntax* syntax;
    const TypeSymbol* type;

    BoundExpression(BoundNodeKind kind, const ExpressionSyntax* syntax, const TypeSymbol* type) :
        BoundNode(kind), syntax(syntax), type(type) {}
};

class BadBoundExpression : public BoundExpression {
public:
    BoundExpression* child;

    BadBoundExpression(BoundExpression* child) :
        BoundExpression(BoundNodeKind::Unknown, nullptr, nullptr), child(child) {}
};

class BoundLiteral : public BoundExpression {
public:
    ConstantValue value;

    BoundLiteral(const ExpressionSyntax* syntax, const TypeSymbol* type, const ConstantValue& value) :
        BoundExpression(BoundNodeKind::Literal, syntax, type), value(value) {}

    BoundLiteral(const ExpressionSyntax* syntax, const TypeSymbol* type, ConstantValue&& value) :
        BoundExpression(BoundNodeKind::Literal, syntax, type), value(std::move(value)) {}
};

class BoundParameter : public BoundExpression {
public:
    const ParameterSymbol& symbol;

    BoundParameter(const ExpressionSyntax* syntax, const ParameterSymbol& symbol) :
        BoundExpression(BoundNodeKind::Parameter, syntax, symbol.type), symbol(symbol) {}
};

class BoundUnaryExpression : public BoundExpression {
public:
    BoundExpression* operand;

    BoundUnaryExpression(const ExpressionSyntax* syntax, const TypeSymbol* type, BoundExpression* operand) :
        BoundExpression(BoundNodeKind::UnaryExpression, syntax, type), operand(operand) {}
};

class BoundBinaryExpression : public BoundExpression {
public:
    BoundExpression* left;
    BoundExpression* right;

    BoundBinaryExpression(const ExpressionSyntax* syntax, const TypeSymbol* type, BoundExpression* left, BoundExpression* right) :
        BoundExpression(BoundNodeKind::BinaryExpression, syntax, type), left(left), right(right) {}
};

}
