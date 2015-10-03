#pragma once

#include "SyntaxNode.h"
#include "Token.h"

namespace slang {

class ExpressionSyntax : public SyntaxNode {
protected:
    ExpressionSyntax(SyntaxKind kind) : SyntaxNode(kind) {}
};

class PrefixUnaryExpressionSyntax : public ExpressionSyntax {
public:
    Token* operatorToken;
    ExpressionSyntax* operand;

    PrefixUnaryExpressionSyntax(SyntaxKind kind, Token* operatorToken, ExpressionSyntax* operand) :
        ExpressionSyntax(kind), operatorToken(operatorToken), operand(operand)
    {
        childCount += 2;
    }
};

class BinaryExpressionSyntax : public ExpressionSyntax {
public:
    ExpressionSyntax* left;
    Token* operatorToken;
    ExpressionSyntax* right;

    BinaryExpressionSyntax(SyntaxKind kind, ExpressionSyntax* left, Token* operatorToken, ExpressionSyntax* right) :
        ExpressionSyntax(kind), left(left), operatorToken(operatorToken), right(right)
    {
        childCount += 3;
    }
};

class PrimaryExpressionSyntax : public ExpressionSyntax {
};

class LiteralExpressionSyntax : public PrimaryExpressionSyntax {
public:
    Token* literal;
};



}